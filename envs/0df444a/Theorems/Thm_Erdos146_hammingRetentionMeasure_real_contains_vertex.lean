-- Prove2me | Theorems.Thm_Erdos146_hammingRetentionMeasure_real_contains_vertex
-- name    : Erdos146.hammingRetentionMeasure_real_contains_vertex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:49:05.181243+00:00
-- url     : https://prove2.me/theorems/c9efbf84-04d1-4ba2-955b-c50b2120129d
-- title:
--   Probability that a vertex is retained
-- statement:
--   Supporting fact for the sampled Hamming-ball graph of Section 7. The host is the sampled Hamming-ball graph of Section 7: with $U = \{0,1\}^m$, two disjoint copies $U_L, U_R$ are joined whenever their Hamming distance is at most $k = \lfloor \tau m \rfloor$, and each vertex is retained independently with probability $p = 2^{-\beta m}$. A given vertex is retained with probability exactly $p$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L14968-L14977

import Definitions.Def_erdos146_core2
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.hammingRetentionMeasure_real_contains_vertex
    (dimension : ℕ)
    (vertex : Bool × HammingWord dimension) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        vertex ∈ retained} =
      hammingRetentionProbability dimension := by sorry
