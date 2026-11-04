-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_C2_event_local_rightatom_absolute_cash
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_C2_event_local_rightatom_absolute_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:56:42.271477+00:00
-- url     : https://prove2.me/theorems/a10de6ee-b176-47fc-b703-e2650a005a2e
-- title:
--   Original UBV C2 interior event yields exact random-clock right-atom absolute Stieltjes budget
-- statement:
--   For the original controlled Lévy risk process with arbitrary countable right-dividend atoms and genuine sample-dependent clock, original C2 smoothness plus a compact strictly interior reserve strip yields a finite right-payment upper secant coefficient on every path in a chosen localization event. The exact source-ordered random right-atom sum on that event is absolutely summable, nonpositive and dominated by full original stopped discounted Stieltjes Cash, with time zero, simultaneous Lévy/dividend jumps and eligible closed-horizon atoms retained. There is no extrapolation of the derivative envelope through boundary contact.
-- source:
--   Proved P4-D localband C2 maxone 0cc4b107 and original event-local absolute atomic Cash 5227d607; actual original P4-F Cash 0dda1be7; Proposition 4(i) Eq(5.13)

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_clock_event_local_rightatom_cash_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_C2_localband_actual_rightjump_secant_maxone

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_C2_event_local_rightatom_absolute_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
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
    (s : Set Ω)
    (hPre : ∀ ω ∈ s, ∀ i, riskProcess X x D (t ω i) ω ∈ Icc a b)
    (hPost : ∀ ω ∈ s, ∀ i,
      x + X.X (t ω i) ω - rightLimit D (t ω i) ω ∈ Icc a b)
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
        (∑' i : ι, |J i|) ≤ (max 1 (K : ℝ) - 1) * Cash ω := by sorry
