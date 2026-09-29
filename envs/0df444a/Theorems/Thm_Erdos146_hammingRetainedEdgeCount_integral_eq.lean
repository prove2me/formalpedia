-- Prove2me | Theorems.Thm_Erdos146_hammingRetainedEdgeCount_integral_eq
-- name    : Erdos146.hammingRetainedEdgeCount_integral_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:51:12.060261+00:00
-- url     : https://prove2.me/theorems/230070f9-24cb-4fd9-87ab-9b4ac9b5c7c3
-- title:
--   Integral form of the retained edge count
-- statement:
--   Supporting fact for the sampled Hamming-ball graph of Section 7. The host is the sampled Hamming-ball graph of Section 7: with $U = \{0,1\}^m$, two disjoint copies $U_L, U_R$ are joined whenever their Hamming distance is at most $k = \lfloor \tau m \rfloor$, and each vertex is retained independently with probability $p = 2^{-\beta m}$. The retained-edge count integrates to the expected retained edge count.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L16435-L16469

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.hammingRetainedEdgeCount_integral_eq
    (dimension radius : ℕ) :
    (∫ retained,
      hammingRetainedEdgeCount dimension radius retained
        ∂hammingRetentionMeasure dimension) =
      hammingExpectedRetainedEdgeCount dimension radius := by sorry
