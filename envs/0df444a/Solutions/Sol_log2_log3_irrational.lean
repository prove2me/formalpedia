-- Prove2me | solution 1 for log2_log3_irrational
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T00:39:27.060742+00:00
-- url     : https://prove2.me/submissions/a0e2617f-e13b-4596-a21d-e1fa1eae5a3c

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

theorem solution : Irrational (Real.log 2 / Real.log 3) := by
  rintro ⟨q, hq⟩
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hthree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hqpos : 0 < q := by
    exact_mod_cast (show (0 : ℝ) < q by rw [hq]; exact div_pos htwo hthree)
  have hnum : 0 ≤ q.num := (Rat.num_pos.mpr hqpos).le
  have heq : (q.num.natAbs : ℝ) / (q.den : ℝ) = Real.log 2 / Real.log 3 := by
    simpa only [Rat.cast_def, Nat.cast_natAbs, abs_of_nonneg (by exact_mod_cast hnum)] using hq
  have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hlogs : (q.den : ℝ) * Real.log 2 = (q.num.natAbs : ℝ) * Real.log 3 := by
    apply (div_eq_div_iff hden hthree.ne').mp at heq
    linarith
  have hpows : (2 : ℝ) ^ q.den = 3 ^ q.num.natAbs := by
    apply Real.log_injOn_pos (show 0 < (2 : ℝ) ^ q.den by positivity)
      (show 0 < (3 : ℝ) ^ q.num.natAbs by positivity)
    simpa only [Real.log_pow] using hlogs
  have hpowsNat : (2 : ℕ) ^ q.den = 3 ^ q.num.natAbs := by exact_mod_cast hpows
  have hdiv : 2 ∣ (3 : ℕ) ^ q.num.natAbs := by
    rw [← hpowsNat]
    exact dvd_pow_self 2 q.den_ne_zero
  have : 2 ∣ (3 : ℕ) := Nat.prime_two.dvd_of_dvd_pow hdiv
  norm_num at this

#print axioms solution
