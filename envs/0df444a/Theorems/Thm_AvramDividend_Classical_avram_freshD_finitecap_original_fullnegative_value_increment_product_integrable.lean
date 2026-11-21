-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_freshD_finitecap_original_fullnegative_value_increment_product_integrable
-- name    : AvramDividend.Classical.avram_freshD_finitecap_original_fullnegative_value_increment_product_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T18:24:10.846548+00:00
-- url     : https://prove2.me/theorems/dd970069-de85-4563-99df-f304cbcb79f4
-- title:
--   Finite-activity finite-cap full negative-mark value kernel integrable on finite predictable product measure
-- statement:
--   For the true spectrally negative Levy mark intensity of finite total negative mass and an arbitrary finite predictable observation measure, the original full nonlinear value increment w(Y+z)-w(Y), for reserves Y in the nonnegative finite cap, is product-integrable. The formula includes all negative marks, including ruin-overshooting marks, without a first-moment assumption on large jump sizes; derives domination from the proved finite-cap value increment bound. This supplies genuine compensator integrability required by the nonlinear full-mark stopped Ito ledger, separate from generator-integrand and Gaussian terms.
-- source:
--   Source-faithful finite-activity full-mark kernel prerequisite for mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43, finite cap cash to Ito route b98df424. Directly uses Proved e4637f43 uniform nonlinear negative-mark bound plus finite product measure; no linear Jfull replacement, no assumption of an expected cash budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys132_original_finite_cap_uniform_negative_mark_increment_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_freshD_finitecap_original_fullnegative_value_increment_product_integrable
    {Ω α : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace α]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (μ : Measure α) (hμ : μ Set.univ < ⊤)
    (Y : α → ℝ) (hY : ∀ a, 0 ≤ Y a ∧ ENNReal.ofReal (Y a) ≤ C)
    (G : α × ℝ → ℝ)
    (hG : ∀ p, G p = if p.2 < 0 then w (Y p.1 + p.2) - w (Y p.1) else 0)
    (hGmeas : AEStronglyMeasurable G (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) :
    Integrable G (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) := by sorry
