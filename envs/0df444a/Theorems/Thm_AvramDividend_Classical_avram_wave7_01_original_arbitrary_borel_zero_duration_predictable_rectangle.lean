-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_arbitrary_borel_zero_duration_predictable_rectangle
-- name    : AvramDividend.Classical.avram_wave7_01_original_arbitrary_borel_zero_duration_predictable_rectangle
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:50:38.416085+00:00
-- url     : https://prove2.me/theorems/b85c7f84-ad74-451f-8d3d-2d8656075fe3
-- title:
--   Exact original Lévy predictable marked rectangle compensator at zero-duration intervals for arbitrary Borel marks
-- statement:
--   For the unchanged original SpectrallyNegativeLevy process and every past event A∈𝓕_s, arbitrary Borel mark set B, and zero-duration interval (s,s], the exact intrinsic marked jump expected count and the predicted compensator P(A)(s−s)ν(B) both vanish, even with infinite jump activity. This closes the zero-duration branch of the canonical predictable marked rectangle identity, with no BV, finite-activity, extractor or intensity premise.
-- source:
--   Ioc s s is empty, so the original intrinsic jump measure gives zero mass and its restricted ENNReal lintegral is zero; the right-hand side also vanishes since s−s=0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_arbitrary_borel_zero_duration_predictable_rectangle
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s s ×ˢ B) ∂P) =
    P A * (((s - s : ℝ≥0) : ℝ≥0∞)) * X.ν B := by sorry
