-- Prove2me | Theorems.Thm_Erdos146_hammingExpectedRetainedVertexCount_eq
-- name    : Erdos146.hammingExpectedRetainedVertexCount_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:49:17.78075+00:00
-- url     : https://prove2.me/theorems/b683d4fd-0f15-49b0-b2f0-080ead788cad
-- title:
--   Expected number of retained vertices
-- statement:
--   Supporting fact for the sampled Hamming-ball graph of Section 7. The host is the sampled Hamming-ball graph of Section 7: with $U = \{0,1\}^m$, two disjoint copies $U_L, U_R$ are joined whenever their Hamming distance is at most $k = \lfloor \tau m \rfloor$, and each vertex is retained independently with probability $p = 2^{-\beta m}$. The expected number of retained vertices is $p$ times the number of words, i.e. $2^{(1-\beta)m}$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L15050-L15059

import Definitions.Def_erdos146_core2
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.hammingExpectedRetainedVertexCount_eq
    (dimension : ℕ) :
    hammingExpectedRetainedVertexCount dimension =
      2 * hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ) := by sorry
