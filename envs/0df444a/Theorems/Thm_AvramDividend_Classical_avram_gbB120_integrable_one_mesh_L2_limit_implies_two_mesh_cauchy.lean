-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB120_integrable_one_mesh_L2_limit_implies_two_mesh_cauchy
-- name    : AvramDividend.Classical.avram_gbB120_integrable_one_mesh_L2_limit_implies_two_mesh_cauchy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T00:14:34.870677+00:00
-- url     : https://prove2.me/theorems/fcc39741-2337-4371-a7ab-dfb18412fd37
-- title:
--   Integrable one-mesh L2 limit implies two-mesh square-energy Cauchy
-- statement:
--   The elementary but source-reusable Hilbert-space energy bridge. For an arbitrary measure and functions with integrable pairwise squared errors and integrable squared error to a common limit, convergence of the single-index error integral to zero forces product-index Cauchy convergence of the pairwise squared error. The proof is the pointwise squared triangle bound followed by integral monotonicity and the product-atTop squeeze. This is a necessary analytic bridge between B116 and the B115 refinement energy when applied to the original product measure.

import Mathlib
open MeasureTheory Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB120_integrable_one_mesh_L2_limit_implies_two_mesh_cauchy
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : ℕ → α → ℝ) (g : α → ℝ)
    (hfg : ∀ m, Integrable (fun a => (f m a - g a) ^ 2) μ)
    (hff : ∀ m p, Integrable
      (fun a => (f m a - f p a) ^ 2) μ)
    (hlim : Tendsto
      (fun m => ∫ a, (f m a - g a) ^ 2 ∂μ)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto
      (fun nm : ℕ × ℕ =>
        ∫ a, (f nm.1 a - f nm.2 a) ^ 2 ∂μ)
      atTop (𝓝 (0 : ℝ)) := by sorry
