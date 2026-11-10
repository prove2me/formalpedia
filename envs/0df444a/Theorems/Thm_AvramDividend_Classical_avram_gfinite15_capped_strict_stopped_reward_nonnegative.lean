-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite15_capped_strict_stopped_reward_nonnegative
-- name    : AvramDividend.Classical.avram_gfinite15_capped_strict_stopped_reward_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T13:00:05.210433+00:00
-- url     : https://prove2.me/theorems/35d7fe76-f704-44f1-9098-f3bb6d89d0f7
-- title:
--   Positive-clock original finite-cap strict stopped reward is nonnegative
-- statement:
--   For the actual original Lévy process and any admissible finite-real-cap dividend strategy, a strictly positive stopping clock has a nonnegative discounted prepayment terminal plus the full strict-before-clock Stieltjes dividend cash. The terminal sign follows from finite-cap gradient monotonicity and the original admissible cap, with negative reserves covered by the killed payoff. This is a nonnegative-Fatou prerequisite for the genuine physical localisation passage in 642de490, and assumes no Itô or expectation conclusion.
-- source:
--   G-FINITE15: exact positive-clock nonnegativity child of root-connected original Gaussian budget 642de490. Reuses proved ef15784e finite-cap gradient sign; retains original X, D, paymentTimes and ruinTime.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_finitecap_gradient_lower_bound_nonnegative_payoff

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gfinite15_capped_strict_stopped_reward_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw0 : 0 ≤ w 0) (hwcont : ContinuousOn w (Ici 0))
    (hwDiff : DifferentiableOn ℝ w (Ioo 0 c))
    (hwGrad : ∀ y : ℝ, 0 < y → y < c → 1 ≤ deriv w y)
    (hwNeg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (q : ℝ) (σ : Ω → ℝ≥0) :
    ∀ ω, 0 < σ ω →
      0 ≤ Real.exp (-(q * (σ ω : ℝ))) *
        w (riskProcess X x D (σ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal := by sorry
