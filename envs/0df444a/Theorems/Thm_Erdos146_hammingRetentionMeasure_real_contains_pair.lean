-- Prove2me | Theorems.Thm_Erdos146_hammingRetentionMeasure_real_contains_pair
-- name    : Erdos146.hammingRetentionMeasure_real_contains_pair
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:48:52.683157+00:00
-- url     : https://prove2.me/theorems/6f05ee53-14d9-4289-9ddc-620160cffdd3
-- title:
--   Probability that a pair is retained
-- statement:
--   Supporting fact for the sampled Hamming-ball graph of Section 7. The host is the sampled Hamming-ball graph of Section 7: with $U = \{0,1\}^m$, two disjoint copies $U_L, U_R$ are joined whenever their Hamming distance is at most $k = \lfloor \tau m \rfloor$, and each vertex is retained independently with probability $p = 2^{-\beta m}$. A given pair of distinct vertices is retained with probability $p^2$, by independence.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L14956-L14966

import Definitions.Def_erdos146_core2
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.hammingRetentionMeasure_real_contains_pair
    (dimension : ℕ)
    (first second : Bool × HammingWord dimension)
    (hdistinct : first ≠ second) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        first ∈ retained ∧ second ∈ retained} =
      hammingRetentionProbability dimension ^ 2 := by sorry
