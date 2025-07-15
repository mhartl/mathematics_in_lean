import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

#check (le_max_left a b : a ≤ max a b)
#check (le_max_right a b : b ≤ max a b )
#check (max_le : a ≤ c → b ≤ c → max a b ≤ c)

example : min a b ≤ min b a := by
  -- Goal 1: `c ≤ a →`
  -- Goal 2: `c ≤ b →`
  -- Conclusion: `b ≤ min a b`
  -- The example is `min a b ≤ min b a`, which has the form
  --   `min a b ≤ b → min a b ≤ a → min a b ≤ min b a`
  -- Note in particular that `min b a` on the right-hand side reverses the
  -- order of `a` and `b` from the definition. This gives the subgoals
  -- Goal 1: `min a b ≤ b →`
  -- Goal 2: `min a b ≤ a →`
  -- Conclusion: `min a b ≤ min b a`
  -- Applying `le_min` introduces the goals
  -- 1. `min a b ≤ b`
  -- 2. `min a b ≤ a`
  apply le_min
    -- Fulfills `min a b ≤ b`
  · apply min_le_right
  -- Fulfills `min a b ≤ a`
  apply min_le_left
  -- Since both goals are fulfilled, the relation follows.


example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  -- "The first `apply` after `le_antisymm` implicitly uses `h a b`,
  --  whereas the second one uses `h b a`."
  -- Possibly confusing; see below for an explicit version.
  apply h
  apply h

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  -- Explicit application of both orders of argument
  apply h a b
  apply h b a

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

-- Explicit version
example : max a b = max b a := by
  apply le_antisymm
  · show max a b ≤ max b a
    apply max_le
    · apply le_max_right
    apply le_max_left
  · show max b a ≤ max a b
    apply max_le
    · apply le_max_right
    apply le_max_left

-- Shorter version
example : max a b = max b a := by
  apply le_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  -- Prove min (min a b) c ≤ min a (min b c)
  -- Introduce two subgoals
  · apply le_min
    -- First subgoal: min (min a b) c ≤ a
    · apply le_trans
      apply min_le_left   -- min (min a b) ≤ min a b ≤ a
      apply min_le_left   -- min a b ≤ a ≤ a → Subgoal accomplished
    -- Second subgoal: min (min a b) c ≤ c
    apply le_min
    · apply le_trans
      apply min_le_left
      apply min_le_right
    apply min_le_right
  -- Prove min a (min b c) ≤ min (min a b) c
  -- Introduce two subgoals
  apply le_min
  -- First subgoal: min a (min b c) ≤ min (a b)
  · apply le_min
    -- Introduce two subsubgoals
    -- First subsubgoal: min a (min b c) ≤ a
    · apply min_le_left
    -- Second subsubgoal: min a (min b c) ≤ b
    apply le_trans
    apply min_le_right
    apply min_le_left
  -- Second subgoal: min a (min b c) ≤ c
  apply le_trans
  -- Show that min a (min b c) ≤ c
  apply min_le_right  -- min (b c) ≤ c
  apply min_le_right  -- c ≤ c


-- Grok's initial (incorrect) answer
example : b ≤ max a (max b c) := by
  apply le_trans
  · apply le_max_left
  apply le_max_right

-- Grok's answer after some prodding
example : b ≤ max a (max b c) := by
  apply le_trans
    -- Explicit: proves b ≤ max b c, setting ?m := max b c
  · exact le_max_left b c
  -- Explicit: proves max b c ≤ max a (max b c)
  exact le_max_right a (max b c)

example : b ≤ max a (max b c) := by
  apply le_trans
  -- Need to prove b ≤ max b c ∧ max b c ≤ max a (max b c)
  -- to conclude b ≤ max a (max b c) by transitivity.
  -- Prove b ≤ max b c
  · apply le_max_left b c  -- force args to be `b c`
  -- Prove max b c ≤ max a (max b c)
  apply le_max_right  -- implicit args `a (max b c)`

example : c ≤ max a (max b c) := by
  apply le_trans
  -- Need to prove c ≤ max b c ∧ max b c ≤ max a (max b c)
  -- to conclude c ≤ max a (max b c) by transitivity.
  -- Prove c ≤ max b c
  · apply le_max_right b c  -- force args to be `b c`
  -- Prove max b c ≤ max a (max b c)
  apply le_max_right  -- implicit args `a (max b c)`


example : max (max a b) c = max a (max b c) := by
  apply le_antisymm
  -- Prove max (max a b) c ≤ max a (max b c)
  -- Introduce two subgoals
  apply max_le
    -- Must show:
    --   1. max a b ≤ max a (max b c)
    -- and
    --   2. c ≤ max a (max b c)
    -- 1. subgoal: max a b ≤ max a (max b c)
    -- Introduce two subsubgoals
  · apply max_le
      -- Must show subsubgoals:
      --   1'. a ≤ max a (max b c)
      --   2'. b ≤ max a (max b c)
    -- 1'. a ≤ max a (max b c)
    apply le_max_left
    -- 2'. b ≤ max a (max b c)
    -- Need subsubgoal
    apply le_trans
    -- Need to prove b ≤ max b c ∧ max b c ≤ max a (max b c)
    -- to conclude b ≤ max a (max b c) by transitivity.
    -- Prove b ≤ max b c
    · apply le_max_left b c  -- force args to be `b c`
    -- Prove max b c ≤ max a (max b c)
    apply le_max_right  -- implicit args `a (max b c)`
    -- 2. subgoal: c ≤ max a (max b c)
  · apply le_trans
    · apply le_max_right b c  -- force args to be `b c`
    apply le_max_right  -- implicit args `a (max b c)`

  -- Prove max a (max b c) ≤ max (max a b) c
  apply max_le
  -- 1. a ≤ max (max a b) c
  · apply le_trans
    · apply le_max_left a b
    apply le_max_left
  -- 2. max b c ≤ max (max a b) c
  · apply max_le
      -- Must show subsubgoals:
      --   1'. b ≤ max (max a b) c
      --   2'. c ≤ max (max a b) c
    -- 1'. b ≤ max (max a b) c
    -- Need subsubgoal
    apply le_trans
    -- Need to prove b ≤ max a b ∧ max a b ≤ max (max a b) c
    -- to conclude b ≤ max (max a b) c by transitivity.
    -- Prove b ≤ max a b
    · apply le_max_right a b
    -- Prove max a b ≤ max (max a b) c
    apply le_max_left
    -- 2'. subgoal: max (max a b) c
    apply le_max_right

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  sorry
example : min a b + c = min (a + c) (b + c) := by
  sorry
#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| :=
  sorry

end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x := by
  apply dvd_mul_of_dvd_right
  apply dvd_refl

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  rw [pow_two]
  apply dvd_mul_right


example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  sorry
end

section
variable (m n : ℕ)

-- Attempts to mimic set inclusion.
-- #check (1 : ℕ)
-- #check ¬ (1.0 : ℕ)
-- #check 1 ∈ {n : ℕ | n ≥ 0}
-- #check 0 ∈ {n : ℕ | n > 0}
-- #check (1.0 : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  sorry
end
