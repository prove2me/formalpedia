-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_eventually_unit_finite_measure_tendsto_of_all_test_limits
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_eventually_unit_finite_measure_tendsto_of_all_test_limits
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:30:22.755197+00:00
-- url     : https://prove2.me/theorems/fe2ae4cb-9e15-4808-90cb-e66c1f5da920
-- title:
--   Weak convergence from eventual compact support and all bounded nonnegative tests
-- statement:
--   A finite-measure family on the reals which is eventually supported in [0,1] and eventually has total mass bounded by C converges weakly to the specified finite measure rho whenever the nonnegative bounded continuous test lintegrals converge to their rho integrals. The conclusion is on the original filter, without countability assumptions or a chosen subsequence.

import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
open MeasureTheory Filter Set Topology BoundedContinuousFunction
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_eventually_unit_finite_measure_tendsto_of_all_test_limits
    {ι : Type*} (l : Filter ι)
    (C : ℝ≥0) (μi : ι → FiniteMeasure ℝ) (ρ : FiniteMeasure ℝ)
    (hmass : ∀ᶠ i in l, (μi i).mass ≤ C)
    (hunit : ∀ᶠ i in l, (μi i) (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (hlim : ∀ f : ℝ →ᵇ ℝ≥0,
      Tendsto (fun i => ∫⁻ x, f x ∂μi i) l (nhds (∫⁻ x, f x ∂ρ))) :
    Tendsto μi l (nhds ρ) := by sorry
