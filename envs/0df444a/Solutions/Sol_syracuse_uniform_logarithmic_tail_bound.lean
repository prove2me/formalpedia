-- Prove2me | solution 1 for syracuse_uniform_logarithmic_tail_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-12T22:46:06.053973+00:00
-- url     : https://prove2.me/submissions/180b6139-6015-4d20-a00f-5c22c3eed37a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_weightedLogMassReal
import Definitions.Def_syracuseOrbitMin
import Theorems.Thm_weightedLogMassReal_odd_recip_le_three
import Theorems.Thm_syracuse_uniform_logarithmic_tail_bound_ge_three

theorem solution :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ M x : ℝ, 2 ≤ M → 2 ≤ x →
      weightedLogMassReal (fun n => 0 < n ∧ Odd n)
        (fun n => M < (syracuseOrbitMin n : ℝ)) (fun n => 1 / (n : ℝ)) x
        ≤ C / Real.rpow (Real.log M) c := by
  obtain ⟨C₁, c, hC₁, hc, hcore⟩ := syracuse_uniform_logarithmic_tail_bound_ge_three
  refine ⟨max C₁ (3 * Real.rpow (Real.log 3) c), c, ?_, hc, ?_⟩
  · exact lt_of_lt_of_le hC₁ (le_max_left _ _)
  · intro M x hM hx
    have hlogM : 0 < Real.log M := Real.log_pos (by linarith)
    have hrpos : 0 < Real.rpow (Real.log M) c := Real.rpow_pos_of_pos hlogM c
    by_cases hM3 : 3 ≤ M
    · refine le_trans (hcore M x hM3 hx) ?_
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.mpr hrpos.le)
    · have hmass := weightedLogMassReal_odd_recip_le_three
        (fun n => M < (syracuseOrbitMin n : ℝ)) x hx
      have hrpow : Real.rpow (Real.log M) c ≤ Real.rpow (Real.log 3) c :=
        Real.rpow_le_rpow hlogM.le
          (Real.log_le_log (by linarith) (by linarith)) hc.le
      refine le_trans hmass ?_
      rw [le_div_iff₀ hrpos]
      calc 3 * Real.rpow (Real.log M) c
          ≤ 3 * Real.rpow (Real.log 3) c := by linarith
        _ ≤ max C₁ (3 * Real.rpow (Real.log 3) c) := le_max_right _ _
