-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_capped_grid_scale_tendsto_with_selected_first_crossings
-- name    : AvramDividend.Classical.chat03_capped_grid_scale_tendsto_with_selected_first_crossings
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T14:05:21.28917+00:00
-- url     : https://prove2.me/theorems/e725d808-6736-4a57-98c2-dd7f5e9ae2eb
-- title:
--   Existence and payoff convergence of genuine first crossings on vanishing grids
-- statement:
--   For any finite strict two-sided exit infimum of a spectrally negative Lévy sample path, canonical q-scale W with W(0)=0 and continuous discount, every positive mesh sequence tending to zero admits a sequence of chosen first strict sampled crossing indices eventually. The corresponding capped discounted q-scale values converge to the continuous stopped payoff. The selected indices are defined by finite-index choice rather than assumed in the hypotheses.
-- source:
--   Combines the independently authored eventual strict grid crossing existence and sequential capped stopped-scale convergence once both exact targets have been formally accepted.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_first_grid_crossing_exists_eventually_of_mesh_tendsto
import Theorems.Thm_AvramDividend_Classical_chat03_capped_grid_discounted_scale_mesh_tendsto
import Mathlib.Topology.Order.LeftRightNhds

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_capped_grid_scale_tendsto_with_selected_first_crossings
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
    (hpos : ∀ n, 0 < mesh n) :
    ∃ first : ℕ → ℕ,
      (∀ᶠ n in atTop,
        (X.X ((first n : ℝ≥0) * mesh n) ω < lower ∨
         upper < X.X ((first n : ℝ≥0) * mesh n) ω) ∧
        (∀ j : ℕ, j < first n →
          ¬ (X.X ((j : ℝ≥0) * mesh n) ω < lower ∨
             upper < X.X ((j : ℝ≥0) * mesh n) ω))) ∧
      Tendsto (fun n =>
        discount (min ((first n : ℝ≥0) * mesh n) T) *
          W (x + X.X (min ((first n : ℝ≥0) * mesh n) T) ω))
        atTop
        (𝓝 (discount (min τ T) * W (x + X.X (min τ T) ω))) := by sorry
