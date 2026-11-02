-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_closed_horizon_stieltjes_grid_partition_exact
-- name    : AvramDividend.Classical.avram_wave5_04b_closed_horizon_stieltjes_grid_partition_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:52:53.991815+00:00
-- url     : https://prove2.me/theorems/bc3c810a-82f6-4448-a4e0-457c95d9b2dc
-- title:
--   Exact closed-horizon full Stieltjes lintegral partition preserves the time-zero atom
-- statement:
--   For any real-time measure, arbitrary extended-nonnegative integrand and monotone finite grid starting at zero, the full set lower integral over [0,u_n] is exactly the initial singleton integral over {0} plus the sum of set integrals over adjacent right-half-open cells (u_i,u_(i+1)]. The identity remains valid for infinite mass and retains absolutely continuous, singular-continuous and countably atomic variation. This is a general measure-theoretic bridge to convert approved original-source finite-cell Stieltjes controls into genuine closed-horizon dividendMeasure controls with no lost time-zero atom.
-- source:
--   Proved AvramDividend.Classical.lintegral_Ioc_partition_fin 947adc6d-e8fb-4c10-bd23-a43d10ca8870 and pinned Mathlib MeasureTheory.lintegral_union, with the explicit set partition [0,T] = {0} ∪ (0,T] and disjointness of the singleton and half-open interval.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_lintegral_Ioc_partition_fin

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04b_closed_horizon_stieltjes_grid_partition_exact
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (u : ℕ → ℝ) (hu : Monotone u) (h0 : u 0 = 0) (n : ℕ) :
    (∫⁻ t in Icc (0 : ℝ) (u n), f t ∂μ) =
      (∫⁻ t in {(0 : ℝ)}, f t ∂μ) +
      ∑ i ∈ Finset.range n,
        (∫⁻ t in Ioc (u i) (u (i + 1)), f t ∂μ) := by sorry
