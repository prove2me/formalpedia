-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger32_original_stopping_dividend_cash_vs_clipped_source
-- name    : AvramDividend.Classical.avram_gledger32_original_stopping_dividend_cash_vs_clipped_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T18:17:49.838362+00:00
-- url     : https://prove2.me/theorems/42bb8ee3-741f-46da-a0e5-f3b2ee9e14fa
-- title:
--   Measurable original stopped discounted strict cash controlled by clipped Gaussian source
-- statement:
--   For the original admissible dividend strategy and a genuinely right-continuous-filtration stopping clock bounded by the original ruin and finite horizon, the chronological clipped physical source S_m dominates the strict pre-stop discounted dividend cash and prepayment stopped reward in asymptotic positive L1. This corrects Gaussian27 by requiring the stopping-time hypothesis already present in its parent f77e; without it arbitrary nonmeasurable clocks can defeat the asserted integrability. Use the Proved original four-event identity, derivative-only secant, full pre-ruin Stieltjes cell and strict crossing-cell estimates.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger32_original_stopping_dividend_cash_vs_clipped_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω)
    (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let H : Ω → ℝ := fun ω =>
      if ρ ω = 0 then w x else
        Real.exp (-(q * (ρ ω : ℝ))) *
          w (riskProcess X x D (ρ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
    let S : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i =>
        x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      Finset.sum (Finset.range (m + 1)) (fun i =>
        (E (v (i + 1)) - E (v i)) * w (Y (v i)) +
          E (v (i + 1)) * (w (Z i) - w (Y (v i))))
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => max (H ω - w x - S m ω) (0 : ℝ)) P ∧
      (∫ ω, max (H ω - w x - S m ω) (0 : ℝ) ∂P) ≤ ε := by sorry
