-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_uniform_clipped_grid_eventually_raw
-- name    : AvramDividend.Classical.avram_bv_gen8_original_uniform_clipped_grid_eventually_raw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:49:20.085007+00:00
-- url     : https://prove2.me/theorems/8a693f60-e424-47cf-8ba0-35e04f4586ed
-- title:
--   Exact original stopped BV generator grid clipping agrees pathwise with the raw sum for sufficiently large cutoffs
-- statement:
--   For every path and fixed original BV physical grid, all exact stopped generator cells are finite real numbers and the finitely clipped sum equals the raw generator sum once the cutoff exceeds their absolute-value total. The cutoff can depend on the path and grid. This enables a pathwise clipping-limit bridge without assuming raw-cell L1.
-- source:
--   Exact original process, pre-ruin event and physical generator cells; finite sums and Archimedean choice, without integrability assumptions.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_gen8_original_uniform_clipped_grid_eventually_raw
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ) (ω : Ω) :
    let Z : ℕ → ℝ := fun j => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n j)
    let H : ℕ → ℝ := fun i =>
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z i) - q * w (Z i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    ∃ K0 : ℕ, ∀ K ≥ K0,
      (∑ i ∈ Finset.range (n + 1), max (-(K : ℝ)) (H i)) =
        ∑ i ∈ Finset.range (n + 1), H i := by sorry
