-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gclose17_original_cofinal_strict_reward_left_limit
-- name    : AvramDividend.Classical.avram_gclose17_original_cofinal_strict_reward_left_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T23:09:04.799511+00:00
-- url     : https://prove2.me/theorems/2151ad9a-4187-47c8-83d2-9b08fb95f231
-- title:
--   Original Gaussian strict stopped prepayment reward converges from below along arbitrary increasing cofinal physical clocks
-- statement:
--   On one original zero-jump Gaussian path before or at ruin, any increasing strictly earlier cofinal sequence of physical clock values has its discounted post-rightpayment terminal plus exact strict-before-clock Stieltjes dividend cash converge to the original prepayment terminal plus exact strict-before-stop cash. This handles positive ruin contact without including the right payment atom at the limiting stop. The theorem proves the actual payoff limit, using accepted original cash and discounted terminal convergence, but does not assume a stochastic Ito budget or cofinal stopping-time construction.
-- source:
--   Combine accepted original pathwise Gaussian terminal left limit 99d01208 with accepted arbitrary increasing cofinal strict real cash convergence cea9d467 under unchanged X,D, paymentTimes and dividendMeasure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gfinite15_original_discounted_terminal_left_limit
import Theorems.Thm_AvramDividend_Classical_avram_gclose17_original_strict_cash_real_monotone_cofinal_clock
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gclose17_original_cofinal_strict_reward_left_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (q : ℝ) (hq : 0 < q) :
    ∀ᵐ ω ∂P, ∀ (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) ≤ ruinTime X x D ω →
      ∀ (u : ℕ → ℝ≥0), Monotone u →
        (∀ n, u n < t) → Tendsto u atTop (𝓝[<] t) →
        Tendsto (fun n =>
          Real.exp (-(q * (u n : ℝ))) *
              w (x + X.X (u n) ω - rightLimit D (u n) ω) +
            (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (u n : ℝ),
              ENNReal.ofReal (Real.exp (-(q * s)))
              ∂(dividendMeasure D ω)).toReal)
          atTop
          (𝓝 (Real.exp (-(q * (t : ℝ))) *
              w (riskProcess X x D t ω) +
            (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (t : ℝ),
              ENNReal.ofReal (Real.exp (-(q * s)))
              ∂(dividendMeasure D ω)).toReal)) := by sorry
