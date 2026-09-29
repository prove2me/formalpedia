-- Prove2me | Theorems.Thm_Erdos146_hammingRetentionMeasure_real_contains_finset
-- name    : Erdos146.hammingRetentionMeasure_real_contains_finset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:48:40.769047+00:00
-- url     : https://prove2.me/theorems/f7b20b3b-af09-4c6a-9b62-6d3088c6ae91
-- title:
--   Probability that a finite set is retained
-- statement:
--   Supporting fact for the sampled Hamming-ball graph of Section 7. The host is the sampled Hamming-ball graph of Section 7: with $U = \{0,1\}^m$, two disjoint copies $U_L, U_R$ are joined whenever their Hamming distance is at most $k = \lfloor \tau m \rfloor$, and each vertex is retained independently with probability $p = 2^{-\beta m}$. A given finite set of vertices is retained with probability $p^{|S|}$, by independence.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L14917-L14954

import Definitions.Def_erdos146_core2
import Mathlib.Probability.Distributions.SetBernoulli

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.hammingRetentionMeasure_real_contains_finset
    (dimension : ℕ)
    (required : Finset (Bool × HammingWord dimension)) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        ∀ vertex ∈ required, vertex ∈ retained} =
      hammingRetentionProbability dimension ^ required.card := by sorry
