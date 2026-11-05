-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ae_ordered_rightjump_residual_L1_of_full_cash
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_ae_ordered_rightjump_residual_L1_of_full_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:40:04.561471+00:00
-- url     : https://prove2.me/theorems/5a978e3c-6e3e-4e8a-a9fd-30ce207af4f3
-- title:
--   True original ordered right-dividend jump residual is L1 when the paid cash is L1 and the selected atom sum is measurable
-- statement:
--   For source-correctly ordered right dividend jumps, the existing original pathwise diffuse-and-atomic signed budget provides absolute summability and a bound by (K-1) times the exact paid discounted Stieltjes Cash. Under its almost-sure local interior and secant hypotheses and almost-sure strong measurability of the selected rightjump sum, global L1 integrability of the true original paid Cash forces global L1 integrability of the atomic rightjump residual. The time-zero payment and eligible horizon payment are retained, and the positive ruin right-payment is excluded by the original paymentTimes membership hypotheses.
-- source:
--   Proved full original source pathwise absolute rightjump cash envelope 921d8fc4-b7ac-407e-bcf6-d1848649c1c8. P4-F assumes Integrable Cash. Secant order is original post-Lévy/pre-dividend rightlimit convention.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_interior_diffuse_all_eligible_atomic_signed_cash_budget
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_ae_ordered_rightjump_residual_L1_of_full_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hjump : ∀ ω (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D s ω - D s ω ≤ w (riskProcess X x D s ω) -
        w (riskProcess X x D s ω - (rightLimit D s ω - D s ω)))
    (A : Ω → Set ℝ) (t : Ω → ι → ℝ≥0) (T : Ω → ℝ≥0)
    (K : ℝ) (hK : 1 ≤ K)
    (hA : ∀ᵐ ω ∂P, MeasurableSet (A ω))
    (hregion : ∀ᵐ ω ∂P, ∀ s ∈ A ω,
      0 < riskProcess X x D s.toNNReal ω ∧
      ENNReal.ofReal (riskProcess X x D s.toNNReal ω) < C)
    (hInt : ∀ᵐ ω ∂P, IntegrableOn
      (fun s : ℝ => Real.exp (-(q * s)) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)))
      (A ω) (dividendMeasure D ω))
    (hT : ∀ᵐ ω ∂P, ∀ i, t ω i ≤ T ω)
    (hPre : ∀ᵐ ω ∂P, ∀ i, t ω i = 0 ∨
      (t ω i : ℝ≥0∞) < ruinTime X x D ω)
    (hPay : ∀ᵐ ω ∂P, ∀ i,
      (t ω i : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (hInj : ∀ᵐ ω ∂P, Function.Injective (fun i : ι => (t ω i : ℝ)))
    (hLocalSecant : ∀ᵐ ω ∂P, ∀ i,
      w (riskProcess X x D (t ω i) ω) -
      w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) ≤
        K * (rightLimit D (t ω i) ω - D (t ω i) ω))
    (Cash Atom : Ω → ℝ)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hAtom : ∀ ω, Atom ω = (∑' i : ι, Real.exp (-(q * (t ω i : ℝ))) *
          ((rightLimit D (t ω i) ω - D (t ω i) ω) +
            w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
            w (riskProcess X x D (t ω i) ω))))
    (hCashI : Integrable Cash P)
    (hAtomMeas : AEStronglyMeasurable Atom P) :
    Integrable Atom P := by sorry
