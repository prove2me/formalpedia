-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian17_original_masked_gradient_MemLp
-- name    : AvramDividend.Classical.avram_ubv_gaussian17_original_masked_gradient_MemLp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T19:17:18.283413+00:00
-- url     : https://prove2.me/theorems/498f21c8-74dc-4211-85c0-5efcfb0b99ff
-- title:
--   The original stopped prepayment Gaussian gradient belongs to predictable L²
-- statement:
--   On Avram's original probability space and right-continuous predictable filtration, the clipped original prepayment reserve Gaussian gradient defines an actual MemLp 2 coefficient for every finite predictable-space measure. This closes the conversion from the existing original-source measurable finite squared energy theorem to the Lp integrand required by predictable elementary rectangle approximation and isometric extension. No natural-filtration substitution or change to the original stopping clock is made.
-- source:
--   Existing Proved 7ae1130d plus pinned Mathlib lintegral_ofReal_ne_top_iff_integrable and memLp_two_iff_integrable_sq.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_gaussian_masked_gradient_source_L2

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian17_original_masked_gradient_MemLp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    MemLp G 2 μ := by sorry
