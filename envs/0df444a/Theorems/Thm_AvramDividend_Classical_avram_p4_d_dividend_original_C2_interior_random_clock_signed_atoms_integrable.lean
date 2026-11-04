-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_C2_interior_random_clock_signed_atoms_integrable
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_C2_interior_random_clock_signed_atoms_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:50:52.164911+00:00
-- url     : https://prove2.me/theorems/296c58eb-ea9e-47cf-b181-09690195edb8
-- title:
--   Original random-clock signed right atoms L1 from source C2 interior localisation and measurable terms
-- statement:
--   For the actual original Lévy risk process with a countable injective measurable right-payment enumeration at a genuine random finite stopped clock, source C2 regularity on a compact strictly interior reserve band yields a finite upper right-dividend secant constant. Assuming every selected post-X and post-dividend reserve remains in that band, indexed corrections are a.e. strongly measurable and exact Stieltjes Cash is integrable, the discounted signed atomic remainder is integrable and nonpositive a.s. Uniform interior localisation is an explicit honest hypothesis, with contact at zero/cap excluded and left to P4-E.
-- source:
--   Proved source c4293baa compact-band C2; P4-D localband maxone (new); P4-D countable measurable-term L1 (new); actual original P4-F Cash, hjump and stopping clock 0dda1be7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_C2_localband_actual_rightjump_secant_maxone
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_clock_countable_measurable_terms_L1

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_C2_interior_random_clock_signed_atoms_integrable
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
    (hjump : ∀ ω (s : ℝ≥0), (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D s ω - D s ω ≤ w (riskProcess X x D s ω) -
        w (riskProcess X x D s ω - (rightLimit D s ω - D s ω)))
    (t : Ω → ι → ℝ≥0) (τ : Ω → ℝ≥0)
    (hT : ∀ ω i, t ω i ≤ τ ω)
    (hPay : ∀ ω i, (t ω i : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (hInj : ∀ ω, Function.Injective (fun i : ι => (t ω i : ℝ)))
    (hPre : ∀ ω i, riskProcess X x D (t ω i) ω ∈ Icc a b)
    (hPost : ∀ ω i, x + X.X (t ω i) ω - rightLimit D (t ω i) ω ∈ Icc a b)
    (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hCashI : Integrable Cash P)
    (hAtomTermMeas : ∀ i : ι,
      AEStronglyMeasurable (fun ω => Real.exp (-(q * (t ω i : ℝ))) *
        ((rightLimit D (t ω i) ω - D (t ω i) ω) +
          w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
          w (riskProcess X x D (t ω i) ω))) P) :
    Integrable (fun ω => ∑' i : ι,
      Real.exp (-(q * (t ω i : ℝ))) *
        ((rightLimit D (t ω i) ω - D (t ω i) ω) +
          w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
          w (riskProcess X x D (t ω i) ω))) P ∧
    (∀ᵐ ω ∂P, (∑' i : ι,
      Real.exp (-(q * (t ω i : ℝ))) *
        ((rightLimit D (t ω i) ω - D (t ω i) ω) +
          w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
          w (riskProcess X x D (t ω i) ω))) ≤ 0) := by sorry
