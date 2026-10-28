-- Prove2me | Theorems.Thm_AvramDividend_Classical_nnreal_rightContinuous_strict_upper_gap_interval
-- name    : AvramDividend.Classical.nnreal_rightContinuous_strict_upper_gap_interval
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:15:39.885989+00:00
-- url     : https://prove2.me/theorems/7c7f931b-5753-4a19-9135-a59c933ae114
-- title:
--   Right continuity and a strict gap give a genuine nondegenerate future interval entirely below a fixed level
-- statement:
--   Let f be a right-continuous real path on nonnegative time and suppose f(u)<M. Then there is an actual endpoint v>u such that every t in the half-open interval [u,v) satisfies f(t)<M. This converts an eventual property of the right-neighbourhood filter into a genuine real-time interval via Mathlib's exact pinned nhdsGE_basis_Ico. It is the missing topology bridge for the regulator local-time support argument: at a strictly positive reflected drawdown R(u)=S(u)-X(u), right-continuity of X gives a short interval on which the underlying process cannot reach its previous running supremum S(u), so the running record regulator stays constant. This does not assume or prove the Itô excursion law.
-- source:
--   Pinned Mathlib.Topology.Order.LeftRightNhds.nhdsGE_basis_Ico and ContinuousWithinAt.eventually, Iio_mem_nhds.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.Order.Basic

open AvramDividend.Classical Filter Set Topology
open scoped NNReal

theorem AvramDividend.Classical.nnreal_rightContinuous_strict_upper_gap_interval
    (f : ℝ≥0 → ℝ) (u : ℝ≥0) (M : ℝ)
    (hRight : ContinuousWithinAt f (Ici u) u)
    (hGap : f u < M) :
    ∃ v : ℝ≥0, u < v ∧
      ∀ t : ℝ≥0, u ≤ t → t < v → f t < M := by sorry
