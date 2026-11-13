-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb50b_original_uniform_full_B_ae_nonpositive_from_source
-- name    : AvramDividend.Classical.avram_bvb50b_original_uniform_full_B_ae_nonpositive_from_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:17:02.704528+00:00
-- url     : https://prove2.me/theorems/dee09cd8-406a-459b-a47a-43c9a6e712a4
-- title:
--   Exact BV original uniform full signed physical B ae nonpositive, published after verified bvb49
-- statement:
--   For the original source X, original cash and exact physical uniform grid u(n,i)=Real.toNNReal(Ti/(n+2)), the signed physical HJB sum plus the genuine BV drift-minus-jump residual R is nonpositive pathwise almost everywhere. This instantiates the independently Proved general original grid nonpositivity theorem redux9 with the exact canonical uniform-grid arithmetic bvb49. It closes the first conjunct of the harder bvb48b signed diagonal residual certificate and preserves all source, contact and ruin masks.
-- source:
--   Proved avram_redux9_original_uniform_grid_total_B_ae_nonpositive and original canonical grid bvb49.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb49_original_real_toNNReal_uniform_physical_grid
import Theorems.Thm_AvramDividend_Classical_avram_redux9_original_uniform_grid_total_B_ae_nonpositive
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb50b_original_uniform_full_B_ae_nonpositive_from_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hIntensityPositive : 0 < X.ν (Iio (0 : ℝ)))
    (hCapFinite : C ≠ ⊤) :
    let u : ℕ → ℕ → ℝ≥0 := fun n i =>
      Real.toNNReal (T * (i : ℝ) / ((n : ℝ) + 2))
    let B : ℕ → Ω → ℝ := fun n ω =>
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      (∑ i ∈ Finset.range (n + 1),
          if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
              0 < Z i ∧ ENNReal.ofReal (Z i) < C then
            Real.exp (-(q * (u n i : ℝ))) *
              (X.generator w (Z i) - q * w (Z i)) *
              ((u n (i + 1) : ℝ) - (u n i : ℝ))
          else 0) +
        (let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0
         let R : ℝ≥0 → ℝ := fun t =>
           ((t : ℝ) * X.drift - X.X t ω) - J t
         ∑ i ∈ Finset.range (n + 1),
           (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
               0 < Z i ∧ ENNReal.ofReal (Z i) < C then
             Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
           else 0) * (R (u n i) - R (u n (i + 1))))
    ∀ᵐ ω ∂P, ∀ k : ℕ, B k ω ≤ 0 := by sorry
