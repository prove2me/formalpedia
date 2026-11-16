-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_half_affine_preruin_nonnegative
-- name    : AvramDividend.Classical.avram_bvb_obstruction_original_half_affine_preruin_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:38:45.656098+00:00
-- url     : https://prove2.me/theorems/98d329b8-a5be-46ae-b540-0dce3d15c842
-- title:
--   Half-unit affine verification candidate is nonnegative on every original pre-ruin risk reserve
-- statement:
--   For any original spectrally negative Lévy source, dividend strategy and risk process, the candidate w(u)=0 below zero and u+1/2 otherwise is nonnegative at each positive time strictly before original ruin. This supplies hw_nonneg in the original BV pathwise contact-budget theorem without additional candidate assumptions.
-- source:
--   Proved riskProcess_nonnegative_strictly_before_ruin gives reserve≥0; evaluate the conditional affine candidate on the nonnegative branch.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonnegative_strictly_before_ruin
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bvb_obstruction_original_half_affine_preruin_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) :
    ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ (if riskProcess X x D t ω < 0 then 0
         else 1 / 2 + riskProcess X x D t ω) := by sorry
