-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_positive_cap_bv_zero_horizon_analytic_minimal_hypotheses
-- name    : AvramDividend.Classical.avram_wave7_09_positive_cap_bv_zero_horizon_analytic_minimal_hypotheses
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:46:32.376146+00:00
-- url     : https://prove2.me/theorems/3dbbb604-5366-4b50-8417-a88926af24b0
-- title:
--   Exact positive-cap BV time-zero Stieltjes bound with minimal analytic hypotheses
-- statement:
--   At exact real horizon T=0, the corrected positive-cap BV original discounted Stieltjes payout is bounded by ofReal(w x) under just BV membership, 0<C, 0≤w 0, continuity on nonnegative reserves, interior C1 regularity and gradient floor, cap compatibility and source-admissible D. X.Standing, positivity of discount q, the HJB generator inequality, w=0 on negative reserves, and any positive-time pre-ruin candidate-value sign hypothesis are unnecessary, as the exact stopped Stieltjes integral is only the original initial right atom. The full proof uses Proved original gradient right-jump control 2cd50555, capped post-payment reserve 2ecd3672, BV full-cap secant 2ba5cc4f and exact initial Stieltjes atom budget cd2d62d3.
-- source:
--   The exact original X,P,filtration, ruinTime,paymentTimes,dividendMeasure; pruned proof of Proved W7-09 zero-horizon ac7198c5, no Open dependencies.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_positive_cap_bv_zero_horizon_analytic_minimal_hypotheses
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (q : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x)  := by sorry
