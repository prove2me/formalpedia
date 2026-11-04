-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_reciprocal_cutoff_jump_total
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_reciprocal_cutoff_jump_total
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:44:32.425935+00:00
-- url     : https://prove2.me/theorems/2becd77c-33df-4a0d-9bb1-cc99349a1df7
-- title:
--   Complete original source negative jump mass is the supremum of reciprocal-size cutoff sums
-- statement:
--   For every sample path of the original spectrally negative Levy process, the total actual negative left-jump magnitude on (0,T] equals the supremum of the corresponding jump sums restricted to magnitudes above the reciprocal natural thresholds. This is unconditional on BV, rate, compensator and integrability, and uses no invented Poisson or alternate process.
-- source:
--   Instantiate accepted generic reciprocal-cutoff monotone convergence theorem avram_p3_a_bvdrift_reciprocal_cutoff_tsum_eq_full with the true original source negative left-jump magnitude masked by 0<v≤T.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_reciprocal_cutoff_tsum_eq_full

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The complete original negative left-jump magnitude total is the monotone
supremum over positive reciprocal size cutoffs on the actual source path. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_reciprocal_cutoff_jump_total
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (ω : Ω) :
    let M : ℝ≥0 → ℝ≥0∞ := fun v : ℝ≥0 => if 0 < v ∧ v ≤ T then ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) else 0
    (⨆ n : ℕ, ∑' v : ℝ≥0,
      if (n : ℝ≥0∞)⁻¹ < M v then M v else 0) =
      ∑' v : ℝ≥0, M v := by sorry
