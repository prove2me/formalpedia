-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
-- name    : AvramDividend.Classical.avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:47:27.000872+00:00
-- url     : https://prove2.me/theorems/d6705e01-60f2-4da0-903a-eb818a1b2c1a
-- title:
--   Original BV complement: positive horizon, strict drift slack and sharp real expected Stieltjes cash envelope
-- statement:
--   In the genuine bounded-variation Lévy dividend model, the strict complement of the initial HJB candidate's deterministic drift envelope forces a positive horizon and positive physical drift. Its excess over w(x) is strictly positive; the original full stopped real Stieltjes cash expectation at that horizon is bounded by the sharp physical drift allowance. This isolates the genuinely necessary additional HJB gain without claiming the final w(x) bound.
-- source:
--   Original Avram Dividend Classical BV source; proved full-cap secant 2ba5cc4f and original sharp stochastic real expectation 1bcd326b. Independent complement-specific slack, not the canonical HJB expected cash result.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_sharp_bounded_random_clock_real_cash_mean
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (hEnvelope : ¬ (x + T * X.drift ≤ w x)) :
    0 < T ∧ 0 < X.drift ∧
    0 < (x + T * X.drift - w x) ∧
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
       ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) ≤
       x + T * X.drift := by sorry
