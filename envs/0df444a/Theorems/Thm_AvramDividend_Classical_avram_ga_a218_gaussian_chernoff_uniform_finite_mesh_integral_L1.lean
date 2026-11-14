-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a218_gaussian_chernoff_uniform_finite_mesh_integral_L1
-- name    : AvramDividend.Classical.avram_ga_a218_gaussian_chernoff_uniform_finite_mesh_integral_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:48:49.847633+00:00
-- url     : https://prove2.me/theorems/c5c3007c-3f74-474a-9eaa-8fb8676cfe23
-- title:
--   Gaussian Chernoff exponentially small one-cell mean yields vanishing physical finite-grid expected tail
-- statement:
--   If each source cell has a measurable integrable nonnegative tail envelope and its mean is bounded by exp(b-c(m+1)) uniformly across the physical m-cell grid, then the expected finite sum vanishes by the certified Gaussian exponential cellcount rate. Used in the positive exponential tail of the combined original Gaussian source a216.
-- source:
--   Finite Gaussian Chernoff exponential-tail expectation summation; proved ga_a70; original a216 large-cell source route.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a70_gaussian_physical_mesh_exponential_tail_weighted_cellcount_vanish
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a218_gaussian_chernoff_uniform_finite_mesh_integral_L1
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → ℕ → Ω → ℝ) (b c : ℝ) (hc : 0 < c)
    (hInt : ∀ m i, i < m → Integrable (f m i) P)
    (hPos : ∀ m i ω, 0 ≤ f m i ω)
    (hCell : ∀ m i, i < m →
      (∫ ω, f m i ω ∂P) ≤
        Real.exp (b - c * ((m : ℝ) + 1))) :
    Tendsto (fun m : ℕ =>
      ∫ ω, (∑ i ∈ Finset.range m, f m i ω) ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
