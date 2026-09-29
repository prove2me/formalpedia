-- Prove2me | Theorems.Thm_Erdos146_hammingRetainedVertexCount_integral_eq
-- name    : Erdos146.hammingRetainedVertexCount_integral_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:49:30.630751+00:00
-- url     : https://prove2.me/theorems/504369ff-732a-4d67-9a2f-bebe9bd604db
-- title:
--   Integral form of the retained vertex count
-- statement:
--   Supporting fact for the sampled Hamming-ball graph of Section 7. The host is the sampled Hamming-ball graph of Section 7: with $U = \{0,1\}^m$, two disjoint copies $U_L, U_R$ are joined whenever their Hamming distance is at most $k = \lfloor \tau m \rfloor$, and each vertex is retained independently with probability $p = 2^{-\beta m}$. The retained-vertex count integrates to the expected retained vertex count.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L15196-L15211

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.hammingRetainedVertexCount_integral_eq
    (dimension : ℕ) :
    (∫ retained,
      hammingRetainedVertexCount dimension retained
        ∂hammingRetentionMeasure dimension) =
      hammingExpectedRetainedVertexCount dimension := by sorry
