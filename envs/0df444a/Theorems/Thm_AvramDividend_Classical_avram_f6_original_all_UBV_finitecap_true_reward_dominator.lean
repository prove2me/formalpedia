-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_all_UBV_finitecap_true_reward_dominator
-- name    : AvramDividend.Classical.avram_f6_original_all_UBV_finitecap_true_reward_dominator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:30:27.110059+00:00
-- url     : https://prove2.me/theorems/62859728-5a10-4172-99da-2031b2aa282c
-- title:
--   All UBV true stopped finitecap reward dominated by runningSup plus original cash, including σ=0 purejump
-- statement:
--   For true spectrally negative Levy X of unbounded variation, with no restriction on Gaussian σ, bounded admissible real cash and finite cap, every original stopped payoff of caplinear terminal plus inclusive Stieltjes cash is uniformly bounded by integrable K+x+true runningSup X T+full cash. This replaces the Gaussian-specific runningSup L1 premise using the original positive ψ root theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_all_UBV_finitecap_true_reward_dominator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (hwneg : ∀ y < 0, w y = 0)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (K : ℝ) (hK : ∀ y : ℝ, 0 ≤ y → y ≤ C.toReal → |w y| ≤ K)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτT : ∀ ω, τ ω ≤ T)
    (ρ : ℕ → Ω → ℝ≥0) (hρτ : ∀ m ω, ρ m ω ≤ τ ω)
    (Full : Ω → ℝ)
    (hFull : ∀ ω, Full ω =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal)
    (hFullI : Integrable Full P)
    (Approx : ℕ → Ω → ℝ)
    (hApprox : ∀ m ω, Approx m ω =
      Real.exp (-(q * (ρ m ω : ℝ))) *
        (let z : ℝ :=
           if ρ m ω = 0 ∨ (ρ m ω : ℝ≥0∞) < ruinTime X x D ω
           then x + X.X (ρ m ω) ω - rightLimit D (ρ m ω) ω
           else riskProcess X x D (ρ m ω) ω
         if ENNReal.ofReal z ≤ C then w z
         else w C.toReal + (z - C.toReal)) +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ m ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal) :
    ∃ B : Ω → ℝ, Integrable B P ∧
      ∀ m ω, |Approx m ω| ≤ B ω := by sorry
