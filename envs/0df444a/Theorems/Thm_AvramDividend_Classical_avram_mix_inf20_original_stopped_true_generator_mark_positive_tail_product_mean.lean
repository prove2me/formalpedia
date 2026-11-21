-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_stopped_true_generator_mark_positive_tail_product_mean
-- name    : AvramDividend.Classical.avram_mix_inf20_original_stopped_true_generator_mark_positive_tail_product_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:34:20.17993+00:00
-- url     : https://prove2.me/theorems/92885778-5ed3-44ca-86c7-9028ef90e560
-- title:
--   Original stopped mixed Lévy physical true-truncated generator compensated mark expectation dominated by finite-intensity large-tail discount
-- statement:
--   Actual source-faithful original mixed Lévy stopped physical premark generator kernel, with rightLimit dividend D and exact SpectrallyNegativeLevy.generatorIntegrand using -1<mark<1 truncation. Given finite cap, positive δ≤min(1,C.toReal), and any product/compensator measure μ on time×sample×mark, the expected discounted generator contribution from the above-cap reserve region y>C and negative marks is dominated by the unit-weight *finite-intensity negative tail* mark indicator z≤-δ. This integrates the proved pointwise mark bound using positivity of the discount and standard integral monotonicity. It leaves the real stochastic obligations of μ-integrability and compensator identification explicit. Unlike the fully compensated whole-line source, this is compatible with heavy negative Lévy tails that lack a first moment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mix_inf20_original_stopped_true_generator_mark_positive_tail_product_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ u : ℝ, u < 0 → w u = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) (hδcap : δ ≤ C.toReal)
    (μ : Measure ((ℝ≥0 × Ω) × ℝ)) :
    let V : ℝ → ℝ := fun t =>
      if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal)
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t p.2 - rightLimit D t p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if C.toReal < Y p.1 ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          SpectrallyNegativeLevy.generatorIntegrand V (Y p.1) p.2
      else 0
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if C.toReal < Y p.1 ∧ p.2 < 0 ∧ p.2 ≤ -δ then
        Real.exp (-(q * (p.1.1 : ℝ)))
      else 0
    Integrable H μ → Integrable G μ →
      (∫ p, H p ∂μ) ≤ (∫ p, G p ∂μ) := by sorry
