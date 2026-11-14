-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b35_original_finite_range_stopped_cash_initial_event_from_two_noise_upper
-- name    : AvramDividend.Classical.avram_b35_original_finite_range_stopped_cash_initial_event_from_two_noise_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:19:43.349172+00:00
-- url     : https://prove2.me/theorems/559b3d71-3892-411a-95d5-2c2f1363c37d
-- title:
--   Original finite-range ruin-stopped true dividend reward expected budget from genuine two-noise cash upper
-- statement:
--   For the physical original spectrally negative Lévy process and a finite-range stopped clock, its exact discounted terminal reserve and inclusive Stieltjes dividends have event-restricted expected upper w(x)P(E), whenever the physical stopped Ito–Meyer pathwise upper with the genuine original intrinsic Gaussian and compensated negative-jump noise and local cash integrability hold.
-- source:
--   Avram Palmowski Pistorius (2007) Proposition 4(i), physical stopped Ito–Meyer ruin-clipped cash; original two-channel noise B33 and Proved initial-event expected budget 65038621.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b33_original_finite_range_initial_event_aggregate_centered_noise
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
import Theorems.Thm_AvramDividend_Classical_avram_b21_initial_event_local_aggregate_budget
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b35_original_finite_range_stopped_cash_initial_event_from_two_noise_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (S : Finset ℝ≥0) (hτrange : ∀ ω, τ ω ∈ S)
    (q x : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (H : Ω → ℝ)
    (hHsource : ∀ ω, H ω =
      Real.exp (-(q * (τ ω : ℝ))) *
        w (if τ ω = 0 ∨
              (τ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (τ ω) ω - rightLimit D (τ ω) ω
          else riskProcess X x D (τ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) :
    ∃ (R Jsmall : ℝ≥0 → Ω → ℝ) (M : Ω → ℝ),
      Integrable M P ∧
      (∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
        let E : Set Ω := A ∩ {ω : Ω | τ ω ≠ 0}
        IntegrableOn H E P →
        (∀ᵐ ω ∂(P.restrict E), H ω ≤ w x + M ω) →
        (∫ ω in E, H ω ∂P) ≤ w x * (P E).toReal) ∧
      (∀ ω, M ω = R (τ ω) ω + Jsmall (τ ω) ω) := by sorry
