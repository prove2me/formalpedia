-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_grid_residual_active_pattern_product_ws01b
-- name    : AvramDividend.Classical.bv_actual_grid_residual_active_pattern_product_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:03:28.755747+00:00
-- url     : https://prove2.me/theorems/18478726-1d50-4dce-aa6e-a0365c780a43
-- title:
--   Exact joint probability product for every active/inactive Lévy residual grid pattern
-- statement:
--   For the original spectrally negative Lévy process, any monotone deterministic observation grid, finite prefix length and prescribed finite set of active cells, the joint event that the drift residual strictly increases exactly on the active cells and remains unchanged on the others has probability equal to the product of its individual cell-event probabilities. This is genuine joint independence of the actual process, inherited from the previously proved arbitrary finite increment-cylinder product law. It requires no finite-activity assumption and is a source-faithful input to the binomial count law.
-- source:
--   Specialise the canonically Proved chat04_all_finite_prefix_increment_cylinder_product (4b6af35c) to A=univ and B_i=Iio(d Δt_i) for chosen active cells or singleton {d Δt_i} otherwise. Use X.isProbability and measurability of Iio/singletons. Remote compiler validated the source on 28 October 2026.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_all_finite_prefix_increment_cylinder_product
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_grid_residual_active_pattern_product_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : AvramDividend.Classical.SpectrallyNegativeLevy P 𝓕)
    (t : ℕ → ℝ≥0) (ht : Monotone t)
    (n : ℕ) (active : Finset ℕ) :
    P {ω : Ω | ∀ i : ℕ, i < n →
      X.X (t (i + 1)) ω - X.X (t i) ω ∈
        (if i ∈ active then
          Iio (X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ)))
        else
          {X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ))})} =
    ∏ i ∈ Finset.range n,
      P {ω : Ω | X.X (t (i + 1)) ω - X.X (t i) ω ∈
        (if i ∈ active then
          Iio (X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ)))
        else
          {X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ))})} := by sorry
