-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_agentB_original_strict_interior_contact_cash_sharp_rate
-- name    : AvramDividend.Classical.avram_agentB_original_strict_interior_contact_cash_sharp_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T23:52:05.404729+00:00
-- url     : https://prove2.me/theorems/ef76aedd-d9d7-43ac-b596-dac0e5dbdaaf
-- title:
--   Sharp genuine pre-ruin Stieltjes interior cash/contact mesh bound without exponential inflation
-- statement:
--   On strictly pre-ruin cells of the original stopped physical grid, the sum of discounted actual Stieltjes cash and the postpayment w-reserve contact changes is at most q times the true maximum grid width times the original undiscounted dividend measure on the strict stopped interval (0,rho). This is a sharp strengthening of Proved gledger112 and feeds the top-cap cash-contact correction and gledger37.
-- source:
--   Proved original contact sum gledger99, exact finite Stieltjes cell partition gledger109, interval inclusion Ioc(0,v_k) subset Ioo(0,rho), local finiteness gledger94, and ENNReal.toReal_mono; the published gledger112 proof supplies the mechanical Lean reduction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_agentB_original_strict_interior_contact_cash_sharp_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (n ρ δ : ℝ≥0) (hρn : ρ ≤ n)
    (hρruin : (ρ : ℝ≥0∞) ≤ ruinTime X x D ω)
    (u : ℝ) (hu : 0 ≤ u)
    (hprefix : ∀ t : ℝ≥0, 0 < t → t < ρ →
      u ≤ riskProcess X x D t ω)
    (v : ℕ → ℝ≥0) (hv : Monotone v) (hv0 : v 0 = 0)
    (k : ℕ) (hvk : v k < ρ)
    (hinterior : ∀ i : ℕ, i < k → v (i + 1) < ρ)
    (hwidth : ∀ i : ℕ, i < k →
      (v (i + 1) : ℝ) - (v i : ℝ) ≤ (δ : ℝ))
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    (Finset.sum (Finset.range k) (fun i =>
      (∫⁻ s in Ioc (v i : ℝ) (v (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (v (i + 1) : ℝ))) *
        (w (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω) -
         w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω)))) ≤
    q * (δ : ℝ) *
      (dividendMeasure D ω (Ioo (0 : ℝ) (ρ : ℝ))).toReal := by sorry
