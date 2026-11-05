-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_cluster_bounded_nonnegative_lintegral_eq
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_cluster_bounded_nonnegative_lintegral_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:22:08.599193+00:00
-- url     : https://prove2.me/theorems/b67da360-25c7-45f4-bc7f-df9cba4692f0
-- title:
--   Weak cluster-point lintegral from bounded nonnegative test convergence
-- statement:
--   A weak cluster point of finite real Borel measures inherits the limiting ENNReal lintegral of every bounded continuous nonnegative test function. The result transports the original-law fourth-weighted exponential-image moment limits to a Prokhorov candidate measure using the exact weak-topology evaluation map and Hausdorff uniqueness, without constructing a sequence of finite measures.

import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.Separation.Hausdorff
open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_cluster_bounded_nonnegative_lintegral_eq
    {ι : Type*} (l : Filter ι)
    (μi : ι → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hcluster : MapClusterPt μ l μi)
    (f : ℝ →ᵇ ℝ≥0) (a : ℝ≥0∞)
    (hlim : Tendsto (fun i => ∫⁻ x, f x ∂μi i) l (nhds a)) :
    (∫⁻ x, f x ∂μ) = a := by sorry
