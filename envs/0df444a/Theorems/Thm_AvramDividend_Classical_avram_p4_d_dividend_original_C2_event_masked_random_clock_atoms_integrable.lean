-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_C2_event_masked_random_clock_atoms_integrable
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_C2_event_masked_random_clock_atoms_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:11:03.040212+00:00
-- url     : https://prove2.me/theorems/c44556d9-9bde-4386-8ee3-d71779718a95
-- title:
--   Source C2 interior event yields L1 nonpositive masked actual original right-payment residual
-- statement:
--   For the original UBV controlled dividend process, use C2 regularity and derivative boundedness on a genuine compact reserve band inside 0<y<C to prove a local upper right-payment secant on a measurable localisation event, where each prepayment and postpayment reserve is in the band. Countable measurable original payment terms and full stopped Stieltjes Cash integrability then imply the event-masked source-ordered right-dividend residual is real-integrable and nonpositive almost surely. The full random-clock Cash includes time zero, singular continuous payments elsewhere and eligible horizon right atoms; this theorem is specifically for the right-atomic contribution. Contact at zero/cap and eventual localisation convergence require separate P4-E results.
-- source:
--   Proved localband 0cc4b107; P4-D masked L1 75e4a96f; original P4-F stopped Cash and hjump 0dda1be7; Proposition 4(i), Eq(5.13)

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_C2_event_local_rightatom_absolute_cash

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_C2_event_masked_random_clock_atoms_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [Countable ι]
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ)
    (C : ℝ≥0∞)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0) (hK : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ K)
    (hjump : ∀ ω (r : ℝ≥0), (r = 0 ∨ (r : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D r ω - D r ω ≤ w (riskProcess X x D r ω) -
        w (riskProcess X x D r ω - (rightLimit D r ω - D r ω)))
    (t : Ω → ι → ℝ≥0) (τ : Ω → ℝ≥0)
    (hT : ∀ ω i, t ω i ≤ τ ω)
    (hPay : ∀ ω i, (t ω i : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (hInj : ∀ ω, Function.Injective (fun i : ι => (t ω i : ℝ)))
    (s : Set Ω) (hs : MeasurableSet s)
    (hPre : ∀ ω ∈ s, ∀ i, riskProcess X x D (t ω i) ω ∈ Icc a b)
    (hPost : ∀ ω ∈ s, ∀ i,
      x + X.X (t ω i) ω - rightLimit D (t ω i) ω ∈ Icc a b)
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
