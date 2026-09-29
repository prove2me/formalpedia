-- Prove2me | Theorems.Thm_Erdos146_hammingRetentionMeasure_memLp_two
-- name    : Erdos146.hammingRetentionMeasure_memLp_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:47:49.878845+00:00
-- url     : https://prove2.me/theorems/8d2a772a-0181-47af-8fcf-8fe7f59ce12f
-- title:
--   Retained counts are square-integrable
-- statement:
--   Supporting fact for the sampled Hamming-ball graph of Section 7. The host is the sampled Hamming-ball graph of Section 7: with $U = \{0,1\}^m$, two disjoint copies $U_L, U_R$ are joined whenever their Hamming distance is at most $k = \lfloor \tau m \rfloor$, and each vertex is retained independently with probability $p = 2^{-\beta m}$. The retained counts lie in $L^2$ — the hypothesis the second-moment argument of Section 8 needs.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L14816-L14824

import Definitions.Def_erdos146_core2
import Mathlib.MeasureTheory.Function.L2Space

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.hammingRetentionMeasure_memLp_two
    (dimension : ℕ)
    (observable : Set (Bool × HammingWord dimension) → ℝ) :
    MeasureTheory.MemLp observable 2
      (hammingRetentionMeasure dimension) := by sorry
