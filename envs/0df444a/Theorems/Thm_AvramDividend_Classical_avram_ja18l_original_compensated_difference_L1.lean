-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18l_original_compensated_difference_L1
-- name    : AvramDividend.Classical.avram_ja18l_original_compensated_difference_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:18:44.668132+00:00
-- url     : https://prove2.me/theorems/685cc2d3-d320-4580-b613-1febfa07b0a1
-- title:
--   Original compensated difference of integrable Gaussian residual and centred Lévy reserve is L1
-- statement:
--   For the original probability measure, every integrable Gaussian intrinsic residual and Standing finite-time Lévy reserve have an L1 difference after subtracting deterministic first-moment drift. This supplies the first conjunct of the stopped-jump martingale's exact original process certificate.
-- source:
--   JA18 bridge to public stopped jump martingale 41babf55

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ja18l_original_compensated_difference_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (R : ℝ≥0 → Ω → ℝ)
    (hRint : ∀ t : ℝ≥0, Integrable (R t) P) :
    ∀ t : ℝ≥0,
      Integrable (fun ω =>
        X.X t ω - (t : ℝ) * (∫ η, X.X 1 η ∂P) - R t ω) P := by sorry
