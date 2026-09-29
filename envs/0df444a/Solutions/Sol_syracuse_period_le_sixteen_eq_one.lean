-- Prove2me | solution 1 for syracuse_period_le_sixteen_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T03:28:52.750142+00:00
-- url     : https://prove2.me/submissions/036dd2c9-7673-4d1b-973d-ba8d2466ce74

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_cycle_eq_one_of_margin

/-- Numerical certificate for the margin hypothesis at a fixed period `a`:  `Kb + 1` is the
least exponent with `3 ^ a < 2 ^ (Kb + 1)`, and the single inequality `103 ^ a < 2 ^ (Kb+1) * 34 ^ a`
then upgrades to every admissible `K`. -/
theorem margin_of (a Kb : ℕ) (hlow : 2 ^ Kb ≤ 3 ^ a) (hnum : 103 ^ a < 2 ^ (Kb + 1) * 34 ^ a) :
    ∀ K : ℕ, 3 ^ a < 2 ^ K → 103 ^ a < 2 ^ K * 34 ^ a := by
  intro K hK
  have hKb : Kb + 1 ≤ K := by
    by_contra hcon
    push Not at hcon
    have h2 : (2:ℕ) ^ K ≤ 2 ^ Kb := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h3 : (2:ℕ) ^ (Kb + 1) ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hKb
  calc 103 ^ a < 2 ^ (Kb + 1) * 34 ^ a := hnum
    _ ≤ 2 ^ K * 34 ^ a := Nat.mul_le_mul_right _ h3

/-- **No nontrivial Syracuse cycle of period at most 16.** -/
theorem solution (m a : ℕ) (hm : 0 < m) (ha : 0 < a) (hle : a ≤ 16)
    (hcyc : syracuseStep^[a] m = m) : m = 1 := by
  interval_cases a
  · exact syracuse_cycle_eq_one_of_margin 1 m (by norm_num) hm hcyc (margin_of 1 1 (by norm_num) (by norm_num))
  · exact syracuse_cycle_eq_one_of_margin 2 m (by norm_num) hm hcyc (margin_of 2 3 (by norm_num) (by norm_num))
  · exact syracuse_cycle_eq_one_of_margin 3 m (by norm_num) hm hcyc (margin_of 3 4 (by norm_num) (by norm_num))
  · exact syracuse_cycle_eq_one_of_margin 4 m (by norm_num) hm hcyc (margin_of 4 6 (by norm_num) (by norm_num))
  · exact syracuse_cycle_eq_one_of_margin 5 m (by norm_num) hm hcyc (margin_of 5 7 (by norm_num) (by norm_num))
  · exact syracuse_cycle_eq_one_of_margin 6 m (by norm_num) hm hcyc (margin_of 6 9 (by norm_num) (by norm_num))
  · exact syracuse_cycle_eq_one_of_margin 7 m (by norm_num) hm hcyc (margin_of 7 11 (by norm_num) (by norm_num))
  · exact syracuse_cycle_eq_one_of_margin 8 m (by norm_num) hm hcyc (margin_of 8 12 (by norm_num) (by norm_num))
  · exact syracuse_cycle_eq_one_of_margin 9 m (by norm_num) hm hcyc (margin_of 9 14 (by norm_num) (by norm_num))
  · exact syracuse_cycle_eq_one_of_margin 10 m (by norm_num) hm hcyc (margin_of 10 15 (by norm_num) (by norm_num))
  · exact syracuse_cycle_eq_one_of_margin 11 m (by norm_num) hm hcyc (margin_of 11 17 (by norm_num) (by norm_num))
  · exact syracuse_cycle_eq_one_of_margin 12 m (by norm_num) hm hcyc (margin_of 12 19 (by norm_num) (by norm_num))
  · exact syracuse_cycle_eq_one_of_margin 13 m (by norm_num) hm hcyc (margin_of 13 20 (by norm_num) (by norm_num))
  · exact syracuse_cycle_eq_one_of_margin 14 m (by norm_num) hm hcyc (margin_of 14 22 (by norm_num) (by norm_num))
  · exact syracuse_cycle_eq_one_of_margin 15 m (by norm_num) hm hcyc (margin_of 15 23 (by norm_num) (by norm_num))
  · exact syracuse_cycle_eq_one_of_margin 16 m (by norm_num) hm hcyc (margin_of 16 25 (by norm_num) (by norm_num))
