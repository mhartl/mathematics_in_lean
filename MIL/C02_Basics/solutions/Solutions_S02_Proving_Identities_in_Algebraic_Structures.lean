import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common

variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_assoc : ∀ a b c : R, (a + b) + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_assoc : ∀ a b c : R, (a * b) * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_neg_cancel (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_neg_cancel, add_zero]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  rw [← neg_add_cancel_left a b, h, neg_add_cancel_left]

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  rw [← add_neg_cancel_right a b, h, add_neg_cancel_right]

-- The longer proof I came up with first:
-- theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
--   rw [← add_neg_cancel_right a b, h, add_assoc, add_neg_cancel, add_zero]

#check MyRing.add_zero
#check add_zero

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

theorem mul_zero_alt (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  exact add_left_cancel h

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 * a + 0 := by
    rw [← add_mul, add_zero, add_zero]
  exact add_left_cancel h

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  rw [← neg_add_cancel_left a b, h, add_zero]

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  rw [← add_neg_cancel_right a b, h, zero_add]

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  apply neg_eq_of_add_eq_zero
  rw [neg_add_cancel]

-- theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
--   rw [← neg_add_cancel_left a b, h, add_zero]

-- theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
--   symm
--   apply neg_eq_of_add_eq_zero
--   rw [add_comm, h]

-- theorem neg_zero : (-0 : R) = 0 := by
--   apply neg_eq_of_add_eq_zero
--   rw [add_zero]

-- theorem neg_neg (a : R) : - -a = a := by
--   apply neg_eq_of_add_eq_zero
--   rw [neg_add_cancel]

end MyRing

namespace MyRing
variable {R : Type*} [Ring R]

theorem self_sub (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg, add_neg_cancel]

theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  rw [← one_add_one_eq_two, add_mul, one_mul]

end MyRing

section
variable {G : Type*} [Group G]

namespace MyGroup

theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  have h : (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) = 1 := by
    rw [mul_assoc, ← mul_assoc a⁻¹ a, inv_mul_cancel, one_mul, inv_mul_cancel]
  rw [← h, ← mul_assoc, inv_mul_cancel, one_mul]

theorem mul_one (a : G) : a * 1 = a := by
  rw [← inv_mul_cancel a, ← mul_assoc, mul_inv_cancel, one_mul]

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [← one_mul (b⁻¹ * a⁻¹), ← inv_mul_cancel (a * b), mul_assoc, mul_assoc, ← mul_assoc b b⁻¹,
    mul_inv_cancel, one_mul, mul_inv_cancel, mul_one]

end MyGroup

end
