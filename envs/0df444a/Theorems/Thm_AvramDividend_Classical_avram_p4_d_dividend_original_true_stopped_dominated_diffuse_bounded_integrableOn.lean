-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_true_stopped_dominated_diffuse_bounded_integrableOn
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_true_stopped_dominated_diffuse_bounded_integrableOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:33:54.329356+00:00
-- url     : https://prove2.me/theorems/68f92716-e1e7-4a77-8641-1bd43ceabab4
-- title:
--   Path-dependent original stopped atomless dividend submeasures support bounded signed integrable kernels
-- statement:
--   For any original adapted nondecreasing left-continuous dividend strategy, the actual original dividendMeasure has finite mass on the finite stopped payment set. Every sample-dependent measure ν dominated by that original dividendMeasure, particularly the atomless diffuse witness from the true Stieltjes splitting, inherits finite mass on the same clock. Any ν-almost-everywhere strongly measurable signed kernel with a finite ν-almost-everywhere bound is therefore integrable. This permits a diffuse control kernel to be integrated without requiring its reserve to remain interior at right-payment atoms or assuming all controlled derivative terms globally integrable.
-- source:
--   Source-exact paymentTimes nonnegative theorem 71123237 and original right-continuous dividendMeasure finite interval mass theorem, with pinned IntegrableOn.of_bound. The domination premise is available for the original μdiffuse witness of Proved 51782257.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_true_stopped_dominated_diffuse_bounded_integrableOn
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (ν : Measure ℝ) (hdom : ν ≤ dividendMeasure D ω)
    (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f (ν.restrict (paymentTimes σ ∩ Iic (T : ℝ))))
    (K : ℝ)
    (hK : ∀ᵐ u ∂ν.restrict (paymentTimes σ ∩ Iic (T : ℝ)), ‖f u‖ ≤ K) :
    IntegrableOn f (paymentTimes σ ∩ Iic (T : ℝ)) ν := by sorry
