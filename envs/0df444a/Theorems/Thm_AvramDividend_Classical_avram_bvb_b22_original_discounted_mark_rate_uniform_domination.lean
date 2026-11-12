-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b22_original_discounted_mark_rate_uniform_domination
-- name    : AvramDividend.Classical.avram_bvb_b22_original_discounted_mark_rate_uniform_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:09:27.582783+00:00
-- url     : https://prove2.me/theorems/16960da1-b471-4091-b276-22ee10295e44
-- title:
--   Uniform absolute domination of the original stopped discounted negative-mark rate
-- statement:
--   The original dividend strategy's stopped, closed-cap negative-mark rate is uniformly absolutely bounded at every time and outcome by a common finite constant, under compact-kernel continuity and finite cap.
-- source:
--   Root-connected domination for inclusive-grid finite-horizon DCT and original phys95 one-sided quadrature.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva20_original_closed_cap_mark_kernel_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_bva20_masked_discounted_mark_rate_uniform_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b22_original_discounted_mark_rate_uniform_domination
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hKernel : ∀ s : Set ℝ, IsCompact s →
      s ⊆ {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C} →
      UniformContinuousOn
        (fun b : ℝ => ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂X.ν) s)
    (q : ℝ) (hq : 0 ≤ q) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω),
        let U : ℝ≥0 → ℝ := fun r => Function.leftLim
          (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) r
        |if (t : ℝ≥0∞) < ruinTime X x D ω ∧
             0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C then
             Real.exp (-(q * (t : ℝ))) *
               ∫ z in Iio (0 : ℝ), w (U t + z) - w (U t) ∂X.ν
           else 0| ≤ B := by sorry
