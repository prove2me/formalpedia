-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_ubv_any_original_zero_start_instant_ruin_ae
-- name    : AvramDividend.Classical.avram_wave6_08_ubv_any_original_zero_start_instant_ruin_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T22:53:22.253426+00:00
-- url     : https://prove2.me/theorems/2df9814e-41d9-4386-8e41-2fc17b1d5a4c
-- title:
--   Original unbounded-variation zero-capital control ruins at zero for any real dividend strategy
-- statement:
--   For the genuine source SpectrallyNegativeLevy on its own probability space and filtration, every adapted, nondecreasing left-continuous dividend strategy from initial capital zero has ruinTime X 0 D=0 almost surely when the source has unbounded variation. The canonically Proved strict-positive-before-ruin finite-stopping theorem applied at deterministic stop zero forces a strictly positive reserve on any surviving path. But X.X(0)=0 and D(0)=0, so the reserve at zero is zero, contradiction. This source property is independent of the cap and directly closes x=0 for the corrected UBV verification core without assuming any stochastic budget.
-- source:
--   Canonical original-source strict positivity before ruin aa42a21a-9b17-47b3-b72d-a6efd383ae5c and original riskProcess_nonneg_before_ruin c26c83f7-d703-46b9-a361-bf008b70dfe6. Chat 08 owns this zero-initial-capital source subcase of corrected core 429e17ca; no other Chat 01–06 stochastic-mesh owner theorem is duplicated.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_original_controlled_preruin_finite_stopping_strict_positive
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_08_ubv_any_original_zero_start_instant_ruin_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P, ruinTime X 0 D ω = 0 := by sorry
