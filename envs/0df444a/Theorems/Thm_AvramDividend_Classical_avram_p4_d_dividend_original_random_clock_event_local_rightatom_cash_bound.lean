-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_clock_event_local_rightatom_cash_bound
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_random_clock_event_local_rightatom_cash_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:52:14.050287+00:00
-- url     : https://prove2.me/theorems/5227d607-963a-4f63-b282-a1c577bc74bb
-- title:
--   Actual random-clock original right-dividend atomic cash bound localized to a path event
-- statement:
--   For the true original paymentTimes and literal full stopped Stieltjes cash, the source-ordered discounted right-atom series and its absolute sum are nonpositive/bounded on any specified set of sample paths. The local upper secant hypothesis K is imposed only on this event. This is the genuine event-localization bridge necessary when C2 Lipschitz bounds hold only while both actual prepayment/postpayment reserves remain strictly inside the cap; it does not assert globally false boundary regularity or measurable random selection.
-- source:
--   Proved fd02394f original paymentTimes right-atom absolute cash at deterministic path/horizon; true random stop of P4-F 0dda1be7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_paymentTimes_all_rightjump_budget_no_preruin_premise

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_random_clock_event_local_rightatom_cash_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ)
    (hjump : ∀ ω (s : ℝ≥0), (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D s ω - D s ω ≤ w (riskProcess X x D s ω) -
        w (riskProcess X x D s ω - (rightLimit D s ω - D s ω)))
    (t : Ω → ι → ℝ≥0) (τ : Ω → ℝ≥0)
    (hT : ∀ ω i, t ω i ≤ τ ω)
    (hPay : ∀ ω i, (t ω i : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (hInj : ∀ ω, Function.Injective (fun i : ι => (t ω i : ℝ)))
    (K : ℝ) (hK : 1 ≤ K) (s : Set Ω)
    (hLocalSecant : ∀ ω ∈ s, ∀ i,
      w (riskProcess X x D (t ω i) ω) -
        w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) ≤
          K * (rightLimit D (t ω i) ω - D (t ω i) ω))
    (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω = (∫⁻ u in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * u))) ∂(dividendMeasure D ω)).toReal) :
    ∀ ω ∈ s,
      let J : ι → ℝ := fun i => Real.exp (-(q * (t ω i : ℝ))) *
        ((rightLimit D (t ω i) ω - D (t ω i) ω) +
          w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
          w (riskProcess X x D (t ω i) ω))
      Summable J ∧ (∑' i : ι, J i) ≤ 0 ∧
        Summable (fun i : ι => |J i|) ∧
        (∑' i : ι, |J i|) ≤ (K - 1) * Cash ω := by sorry
