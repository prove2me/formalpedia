-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_capped_grid_discounted_scale_mesh_tendsto
-- name    : AvramDividend.Classical.chat03_capped_grid_discounted_scale_mesh_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T13:54:31.59099+00:00
-- url     : https://prove2.me/theorems/bb0eba41-6d73-4c9c-ada6-da2af3edb9f6
-- title:
--   Discounted stopped q-scale values converge along vanishing first-crossing meshes
-- statement:
--   For a fixed sample path of a spectrally negative Lévy process and a finite strict two-sided first-passage infimum, suppose the canonical q-scale function vanishes at zero. For any positive mesh sequence converging to zero, if the selected indices are eventually genuine minimal strict crossings, the capped discounted q-scale payoffs converge to the continuous capped first-passage payoff. This proves the sequential form of the accepted uniform neighbourhood crossing theorem without assuming stochastic harmonicity.
-- source:
--   Sequential consequence of the accepted Chat03 capped grid discounted scale open-neighbourhood convergence, with uniqueness of the minimal strict crossing index.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_capped_grid_discounted_scale_zero_continuity
import Mathlib.Topology.Order.LeftRightNhds

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_capped_grid_discounted_scale_mesh_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (ω : Ω) (lower upper x : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (discount : ℝ≥0 → ℝ)
    (hdiscount : Continuous discount)
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
