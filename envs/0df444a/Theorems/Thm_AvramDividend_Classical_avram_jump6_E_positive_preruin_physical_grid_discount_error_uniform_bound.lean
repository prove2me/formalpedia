-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_E_positive_preruin_physical_grid_discount_error_uniform_bound
-- name    : AvramDividend.Classical.avram_jump6_E_positive_preruin_physical_grid_discount_error_uniform_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T19:18:26.261361+00:00
-- url     : https://prove2.me/theorems/dc2ca799-e46e-4866-98b2-f5935ae0246d
-- title:
--   Original strictly pre-ruin canonical physical discounted dividend Stieltjes error bounded by q·meshwidth·paid variation
-- statement:
--   Prove pathwise for every canonical mesh j and original strict pre-ruin stopped σ k>0 that the exact discounted right-dividend Stieltjes grid gap plus initial atom and full paymentTimes closed Iic cash is ≤q/(j+1)*(rightLimit D(σ k)-rightLimit D 0). This is the quantitative finite-grid statement behind the positive strict source limit 60fab4ba, preserving C>0 and all Lévy characteristics including Gaussian/infinite ν. Use Proved avram_b240_original_ruinclipped_mixed_allcap_discounted_full_stieltjes_source_sign for each pre-ruin cell, Proved 0feecaa3 canonical stopped discount oscillation, Proved dividendMeasure_Ioc_rightLimit, and hJump at zero. The original finite stopped D variation is nonnegative and finite; the residual vanishes as j→∞. The claim is genuinely stronger than the parent eventual ε-bound and exposes the local cell calculation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_E_positive_preruin_physical_grid_discount_error_uniform_bound
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
      ∀ ω : Ω, (σ k ω ≠ 0 ∧
          (σ k ω : ℝ≥0∞) < ruinTime X x D ω) →
        ∀ j : ℕ,
            let v : ℕ → ℝ≥0 := fun i => min (u j i) (σ k ω)
            let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
            let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
            let Z : ℕ → ℝ := fun i =>
              x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
            (w (x - rightLimit D 0 ω) - w x) +
              (∑ i ∈ Finset.range (m j),
                E (v (i + 1)) * (w (Y (v (i + 1))) - w (Z i))) +
              Cash ω ≤
              q * (1 / ((j + 1 : ℕ) : ℝ)) *
                ((rightLimit D (σ k ω) ω - rightLimit D 0 ω) : ℝ) := by sorry
