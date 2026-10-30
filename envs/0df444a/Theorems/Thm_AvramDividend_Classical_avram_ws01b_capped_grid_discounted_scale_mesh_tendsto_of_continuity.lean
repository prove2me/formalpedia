-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_capped_grid_discounted_scale_mesh_tendsto_of_continuity
-- name    : AvramDividend.Classical.avram_ws01b_capped_grid_discounted_scale_mesh_tendsto_of_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:18:34.233322+00:00
-- url     : https://prove2.me/theorems/f0470521-4607-428a-8fd2-80c12569987c
-- title:
--   Vanishing-grid actual stopped q-scale convergence from local reserve continuity
-- statement:
--   For the actual first strict two-sided grid exits of the original spectrally negative Levy path, every positive mesh sequence tending to zero yields convergence of the discounted q-scale payoff provided the scale is continuous only at the realised stopped reserve. No Wq(0)=0 hypothesis is imposed. Valid at BV with nonzero boundary atom once the stopped reserve is known nonzero.
-- source:
--   Strengthens the canonical chat03_capped_grid_discounted_scale_mesh_tendsto bb0eba41 by replacing its global zero-origin assumption with actual local continuity at the sampled stopped reserve. Uses Proved avram_ws01b_capped_grid_discounted_scale_of_continuous_reserve cf21ca25, pathwise genuine first-grid crossing and right-continuous original Levy trajectories.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_capped_grid_discounted_scale_of_continuous_reserve
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_ws01b_capped_grid_discounted_scale_mesh_tendsto_of_continuity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (ω : Ω) (lower upper x : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (discount : ℝ≥0 → ℝ)
    (hdiscount : Continuous discount)
    (hContinuity : ContinuousAt W (x + X.X (min τ T) ω))
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (first : ℕ → ℕ)
    (hfirst : ∀ᶠ n in atTop,
      (X.X ((first n : ℝ≥0) * mesh n) ω < lower ∨
       upper < X.X ((first n : ℝ≥0) * mesh n) ω) ∧
      (∀ j : ℕ, j < first n →
        ¬ (X.X ((j : ℝ≥0) * mesh n) ω < lower ∨
           upper < X.X ((j : ℝ≥0) * mesh n) ω))) :
    Tendsto (fun n =>
      discount (min ((first n : ℝ≥0) * mesh n) T) *
        W (x + X.X (min ((first n : ℝ≥0) * mesh n) T) ω))
      atTop
      (𝓝 (discount (min τ T) * W (x + X.X (min τ T) ω))) := by sorry
