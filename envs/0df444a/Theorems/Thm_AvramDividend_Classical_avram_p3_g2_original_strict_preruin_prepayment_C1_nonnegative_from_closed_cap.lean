-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_strict_preruin_prepayment_C1_nonnegative_from_closed_cap
-- name    : AvramDividend.Classical.avram_p3_g2_original_strict_preruin_prepayment_C1_nonnegative_from_closed_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T21:40:40.243243+00:00
-- url     : https://prove2.me/theorems/cef3f237-e89b-470b-be3b-86e265347b09
-- title:
--   Original positive-cap BV strict pre-ruin prepayment HJB value is nonnegative from C1 gradient alone
-- statement:
--   For the original capped admissible dividend reserve, each strictly pre-ruin positive-time prepayment reserve has nonnegative HJB candidate value under only nonnegative w(0), C1 regularity, gradient at least one on the positive subcap interior, and continuity at the cap boundary. The original postpayment reserve is nonnegative; right-payment monotonicity puts the prepayment reserve above it. The Proved closed-cap C1 linear lower envelope then gives w(U) >= w(0)+U >= 0, including cap contact. No generator inequality, HJB equality, compensator, equality in law or standing assumption is needed.
-- source:
--   Exact Proved postPaymentReserve_nonnegative_strictly_before_ruin and postPaymentReserve_rightJump_decomposition from cd9655ac proof evidence, plus closed-cap gradient lower envelope fc03f3ac. This directly discharges the hw_nonneg source premise on P3 residual 7bb152c2 and prebudget a19d8b28 from their weaker hypotheses; their stochastic source budget remains Open.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_nonnegative_strictly_before_ruin
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_rightJump_decomposition
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g2_original_strict_preruin_prepayment_C1_nonnegative_from_closed_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0) ) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω) := by sorry
