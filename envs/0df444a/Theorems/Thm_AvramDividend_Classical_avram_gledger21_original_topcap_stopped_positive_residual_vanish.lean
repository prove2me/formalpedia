-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger21_original_topcap_stopped_positive_residual_vanish
-- name    : AvramDividend.Classical.avram_gledger21_original_topcap_stopped_positive_residual_vanish
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T11:26:56.057502+00:00
-- url     : https://prove2.me/theorems/0dd6c9b7-546c-498b-9d9f-019d6012005f
-- title:
--   Original zero-jump compact stopped Gaussian grid positive reward residual tends to zero in mean
-- statement:
--   At every compact true original-process stopped clock, the positive part of the discounted strict prepayment reward minus its initial value and its exact centred physical Gaussian grid martingale has arbitrarily small expectation on fine deterministic meshes. This is a genuine positive-part L1 stochastic Ito–Stieltjes estimate, stronger than a mean payoff budget. It must be established from the original X, D, strict terminal cash, generator sign, compact Taylor modulus, and Gaussian source moments; no second process, arbitrary grid, or asserted auxiliary martingale is allowed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger21_original_topcap_stopped_positive_residual_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
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
    ∀ ε : ℝ, 0 < ε → ∃ m : ℕ, 0 < m ∧
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let M : Ω → ℝ := fun ω =>
        ∑ i ∈ Finset.range m,
          let s : ℝ≥0 := (i : ℝ≥0) * Δ
          if s < ρ ω then
            let y := riskProcess X x D s ω
            let Z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
            Real.exp (-(q * (s : ℝ))) *
              (deriv w y * Z +
                (iteratedDeriv 2 w y / 2) * (Z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
          else 0
      (∫ ω, max (H ω - w x - M ω) (0 : ℝ) ∂P) ≤ ε := by sorry
