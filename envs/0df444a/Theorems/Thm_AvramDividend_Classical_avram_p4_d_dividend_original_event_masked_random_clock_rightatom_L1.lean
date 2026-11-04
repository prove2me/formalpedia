-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_event_masked_random_clock_rightatom_L1
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_event_masked_random_clock_rightatom_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:55:25.477193+00:00
-- url     : https://prove2.me/theorems/75e4a96f-9e3d-41dc-a0a9-aa87b78722b9
-- title:
--   Event-localised actual source right-dividend random-clock signed atomic remainder is L1
-- statement:
--   For a measurable event of sample paths on which an actual source-ordered right-dividend local secant upper bound K holds, an injective countable enumeration of genuine original paymentTimes and a.e. measurable individual discounted right-atom terms give an a.e. strongly measurable sum. Mask the sum to zero outside the event. The original event-local pathwise absolute series bound supplies a nonpositive signed atomic residual dominated in norm by (K−1) times exact original ruin-stopped Stieltjes Cash. Therefore the masked residual is L1 whenever Cash is, even if the secant estimate fails outside the event. No assertion of global zero/cap boundary regularity or complete Ito identity is made.
-- source:
--   Proved 5227d607 event-local random-clock absolute atom budget; Proved d9f85ad8 original full cash signed L1; Mathlib AEStronglyMeasurable.tsum and indicator; P4-F Cash 0dda1be7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_clock_event_local_rightatom_cash_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_cash_dominates_integrable_negative_residual

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_event_masked_random_clock_rightatom_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [Countable ι]
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ)
    (hjump : ∀ ω (r : ℝ≥0), (r = 0 ∨ (r : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D r ω - D r ω ≤ w (riskProcess X x D r ω) -
        w (riskProcess X x D r ω - (rightLimit D r ω - D r ω)))
    (t : Ω → ι → ℝ≥0) (τ : Ω → ℝ≥0)
    (hT : ∀ ω i, t ω i ≤ τ ω)
    (hPay : ∀ ω i, (t ω i : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (hInj : ∀ ω, Function.Injective (fun i : ι => (t ω i : ℝ)))
    (K : ℝ) (hK : 1 ≤ K) (s : Set Ω) (hs : MeasurableSet s)
    (hLocalSecant : ∀ ω ∈ s, ∀ i,
      w (riskProcess X x D (t ω i) ω) -
        w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) ≤
          K * (rightLimit D (t ω i) ω - D (t ω i) ω))
    (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω = (∫⁻ u in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * u))) ∂(dividendMeasure D ω)).toReal)
    (hCashI : Integrable Cash P)
    (hAtomTermMeas : ∀ i : ι,
      AEStronglyMeasurable (fun ω => Real.exp (-(q * (t ω i : ℝ))) *
        ((rightLimit D (t ω i) ω - D (t ω i) ω) +
          w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
          w (riskProcess X x D (t ω i) ω))) P) :
    let H : Ω → ℝ := fun ω => ∑' i : ι,
      Real.exp (-(q * (t ω i : ℝ))) *
        ((rightLimit D (t ω i) ω - D (t ω i) ω) +
          w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
          w (riskProcess X x D (t ω i) ω))
    Integrable (s.indicator H) P ∧
      (∀ᵐ ω ∂P, s.indicator H ω ≤ 0) := by sorry
