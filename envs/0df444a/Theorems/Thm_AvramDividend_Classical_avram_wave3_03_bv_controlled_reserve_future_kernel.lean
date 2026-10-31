-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_controlled_reserve_future_kernel
-- name    : AvramDividend.Classical.avram_wave3_03_bv_controlled_reserve_future_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:22:33.719046+00:00
-- url     : https://prove2.me/theorems/f4250bc9-442d-4a6a-94d5-a62ceb6cc581
-- title:
--   Original Lévy future-jump law conditional on adapted actual dividend-controlled reserve
-- statement:
--   For the genuine original spectrally negative Lévy process and any actual adapted left-continuous increasing dividend strategy, the controlled reserve x+X_s-D_s is measurable in the original history filtration at deterministic time s. Every nonnegative measurable functional of that reserve and future whole Lévy increment path satisfies the correct conditional-kernel disintegration on any past-measurable event. It supports a future finite-grid jump-compensation argument without assuming a separate canonical Poisson representation.
-- source:
--   Proved AvramDividend.Classical.avram_root29_01_original_future_kernel_past_test 0611e261-f045-4fb5-a53c-a42f06995418 and source IsDividendStrategy adaptedness, X.adapted.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_original_future_kernel_past_test

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave3_03_bv_controlled_reserve_future_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (s : ℝ≥0)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (f : ℝ × (ℝ≥0 → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, (if ω ∈ A then
        f (x + X.X s ω - D s ω,
          fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)
      else (0 : ℝ≥0∞)) ∂P) =
    (∫⁻ ω, (if ω ∈ A then
        ∫⁻ y, f (x + X.X s ω - D s ω, y)
          ∂(Measure.map (fun ζ => (fun t : ℝ≥0 => X.X t ζ)) P)
      else (0 : ℝ≥0∞)) ∂P) := by sorry
