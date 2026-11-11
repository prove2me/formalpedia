-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin19_original_spatial_reward_eventwise_fatou_from_exact_cofinal
-- name    : AvramDividend.Classical.avram_mix_fin19_original_spatial_reward_eventwise_fatou_from_exact_cofinal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T07:30:36.277809+00:00
-- url     : https://prove2.me/theorems/ff307c5e-7dbf-4536-947d-921743b34d07
-- title:
--   Original bounded-clock source positive-event Fatou transfer from exact cofinal spatial stops
-- statement:
--   For original X and physical after-right-payment terminal plus inclusive cash, a.e. cofinal spatial stopped clocks and source-exact eventually identical rewards turn uniformly bounded positive-clock localised L1 expectation budgets into the original positive-clock event budget. Exact endpoint cofinality is Proved 5e436f12, masked Fatou Proved f78a9ca3. The actual stopped local Ito reward bound remains an independent physical premise. No artificial global large-mark martingale.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin18_original_bounded_clock_cofinal_full_reward_eventually_exact
import Theorems.Thm_AvramDividend_Classical_avram_gfinite29_original_masked_positive_event_fatou
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin19_original_spatial_reward_eventwise_fatou_from_exact_cofinal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (σ : Ω → ℝ≥0)
    (hσbound : ∀ ω, (σ ω : ℝ≥0∞) ≤ (n : ℝ≥0∞))
    (S : ℕ → Ω → ℝ≥0∞)
    (hSmono : ∀ ω, Monotone (fun k => S k ω))
    (hSsup : ∀ᵐ ω ∂P, (⨆ k : ℕ, S k ω) = ⊤)
    (σk : ℕ → Ω → ℝ≥0)
    (hσk : ∀ k ω, σk k ω = (min (σ ω : ℝ≥0∞) (S k ω)).toNNReal)
    (F : Ω → ℝ) (Fk : ℕ → Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFksource : ∀ k ω, Fk k ω =
      Real.exp (-(q * (σk k ω : ℝ))) *
        w (if σk k ω = 0 ∨
              (σk k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σk k ω) ω - rightLimit D (σk k ω) ω
          else riskProcess X x D (σk k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σk k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hσmeas : Measurable σ)
    (hσkmeas : ∀ k, Measurable (σk k))
    (hσkle : ∀ k ω, σk k ω ≤ σ ω)
    (hFmeas : AEStronglyMeasurable F P)
    (hFkmeas : ∀ k, Measurable (Fk k))
    (hFkint : ∀ k, Integrable (Fk k) P)
    (hFpos : ∀ ω, σ ω ≠ 0 → 0 ≤ F ω)
    (hFkpos : ∀ k ω, σk k ω ≠ 0 → 0 ≤ Fk k ω)
    (A : Set Ω) (hA : MeasurableSet A)
    (b : ℝ) (hb : 0 ≤ b)
    (hBudget : ∀ k,
      (∫ ω in A ∩ {η : Ω | σk k η ≠ 0}, Fk k ω ∂P) ≤ b) :
    (∫ ω in A ∩ {η : Ω | σ η ≠ 0}, F ω ∂P) ≤ b := by sorry
