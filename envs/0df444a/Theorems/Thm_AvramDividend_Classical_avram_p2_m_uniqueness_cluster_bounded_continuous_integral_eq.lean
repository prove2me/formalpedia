-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_cluster_bounded_continuous_integral_eq
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_cluster_bounded_continuous_integral_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:15:41.921198+00:00
-- url     : https://prove2.me/theorems/308b8c09-9797-4331-bd12-aa4ce41e8d5d
-- title:
--   Cluster-point integral identified by bounded continuous test convergence
-- statement:
--   Let finite real Borel measures have a weak cluster point along a filter. Whenever the integrals of a fixed bounded continuous real test converge to a number a along the same filter, the integral against the cluster-point measure equals a. This follows from continuity of finite-measure integration and uniqueness of real Hausdorff cluster limits; it is a generic exact bridge for identifying the original-process Lévy candidate moments after compactification.

import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.Separation.Hausdorff
open MeasureTheory Filter Topology BoundedContinuousFunction

theorem AvramDividend.Classical.avram_p2_m_uniqueness_cluster_bounded_continuous_integral_eq
    {ι : Type*} (l : Filter ι)
    (μi : ι → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hcluster : MapClusterPt μ l μi)
    (f : ℝ →ᵇ ℝ) (a : ℝ)
    (hlim : Tendsto (fun i => ∫ x, f x ∂μi i) l (nhds a)) :
    (∫ x, f x ∂μ) = a := by sorry
