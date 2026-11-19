-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_E_original_ruin_contact_discounted_physical_Stieltjes_gap_nonpos_limsup
-- name    : AvramDividend.Classical.avram_jump6_E_original_ruin_contact_discounted_physical_Stieltjes_gap_nonpos_limsup
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T18:59:58.710195+00:00
-- url     : https://prove2.me/theorems/650d52e8-9cbe-4418-add1-c1611ae7ed44
-- title:
--   Positive ruin-contact exact physical right-dividend Stieltjes residual and terminal jump limsup nonpositive
-- statement:
--   Under original mixed UBV Levy with ν(Iio0)=∞ and nonzero Gaussian, C>0, any σ_k≤ruin∧n meeting positive contact σ_k=ruin, prove discounted original physical canonical-grid postpayment right-dividend Stieltjes gap plus initial time-zero atom plus terminal ruin-contact W jump plus the exact closed Iic cash has limsup≤0. The Proved exact algebraic identity c168c6c6 cancels all generator/stochastic Source summands from the original grid parent; this child is precisely the remaining genuine physical Stieltjes-to-cash/contact limit. Use Proved discounted payment sum sign 32f95ab5, right-jump Stieltjes measure controls d2232fa0 and positive contact tail 3559180a where applicable. Preserve the original natural ruin time, m(j)=(n+1)(j+1), u(j,i)=i/(j+1), rightLimit D, zero payment atom and endpoint contact.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_E_original_ruin_contact_discounted_physical_Stieltjes_gap_nonpos_limsup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
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
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P)
    (hInfiniteActivity : X.ν (Iio (0 : ℝ)) = ⊤) :
    ∀ k : ℕ,
      let Cash : Ω → ℝ := fun ω : Ω =>
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
      let u : ℕ → ℕ → ℝ≥0 := fun j i =>
        (i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)
      let m : ℕ → ℕ := fun j => (n + 1) * (j + 1)
      ∀ᵐ ω ∂P, (0 < σ k ω ∧ (σ k ω : ℝ≥0∞) = ruinTime X x D ω) →
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ j in atTop,
            let v : ℕ → ℝ≥0 := fun i => min (u j i) (σ k ω)
            let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
            let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
            let Z : ℕ → ℝ := fun i =>
              x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
            (w (x - rightLimit D 0 ω) - w x) +
              (∑ i ∈ Finset.range (m j),
                E (v (i + 1)) * (w (Y (v (i + 1))) - w (Z i))) +
              E (σ k ω) * (w (riskProcess X x D (σ k ω) ω) -
                w (Y (σ k ω))) + Cash ω ≤ ε:= by sorry
