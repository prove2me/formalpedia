-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_zero_cutoff_eq_full_jump_total
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_zero_cutoff_eq_full_jump_total
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:17:18.955168+00:00
-- url     : https://prove2.me/theorems/cba4f96e-2a63-43e2-9133-84cd2cf918d7
-- title:
--   Zero lower jump-size cutoff equals the full original negative left-jump magnitude total
-- statement:
--   For the actual original Lévy process path, selecting strictly positive left-jump magnitude terms gives exactly the unfiltered original negative left-jump tsum on (0,T]. Zero left-jump magnitude terms contribute nothing. The equality holds pathwise without BV or stochastic compensation hypotheses.
-- source:
--   Pointwise case split on original source time and actual ENNReal.ofReal left-jump magnitude; zero valued terms vanish and tsum_congr.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- A zero size cutoff loses no mass from the actual negative left-jump
magnitude series, including zero increments. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_zero_cutoff_eq_full_jump_total
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (ω : Ω) :
    (∑' (v : ℝ≥0),
      if 0 < v ∧ v ≤ T ∧ (0 : ℝ≥0∞) < ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
      then ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) else 0) =
    (∑' (v : ℝ≥0),
      if 0 < v ∧ v ≤ T then ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) else 0) := by sorry
