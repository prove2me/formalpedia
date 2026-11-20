-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_mixed_finitecap_actual_reward_L1_dominator
-- name    : AvramDividend.Classical.avram_f6_original_mixed_finitecap_actual_reward_L1_dominator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T18:59:25.107533+00:00
-- url     : https://prove2.me/theorems/366614ca-c879-44ba-9e56-ddfe2c242c66
-- title:
--   Original finite-cap mixed Gaussian jump stopped caplinear reward dominated by integrable true runningSup plus full cash
-- statement:
--   When original spectrally negative Lévy X has positive Gaussian coefficient and finite cap C, w zero on negative values and bounded on [0,C], and the original full τ discounted Stieltjes cash is integrable, every true clipped subclock payoff (original caplinear postpayment terminal plus inclusive dividend cash) admits one integrable dominating random variable K+x+runningSup X T+Cashτ, for any actual subordinate physical clock ρ≤τ≤T.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_mixed_finitecap_actual_reward_L1_dominator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : 0 < X.σ)
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
