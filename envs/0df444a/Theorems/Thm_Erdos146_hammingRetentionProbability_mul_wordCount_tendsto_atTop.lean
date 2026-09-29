-- Prove2me | Theorems.Thm_Erdos146_hammingRetentionProbability_mul_wordCount_tendsto_atTop
-- name    : Erdos146.hammingRetentionProbability_mul_wordCount_tendsto_atTop
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:47:00.189923+00:00
-- url     : https://prove2.me/theorems/c0a0106a-ea4f-4695-9359-d12e763747f8
-- title:
--   Retention probability times word count tends to infinity
-- statement:
--   Supporting fact for the sampled Hamming-ball graph of Section 7. The host is the sampled Hamming-ball graph of Section 7: with $U = \{0,1\}^m$, two disjoint copies $U_L, U_R$ are joined whenever their Hamming distance is at most $k = \lfloor \tau m \rfloor$, and each vertex is retained independently with probability $p = 2^{-\beta m}$. Since $\beta < 1$, the expected number of retained vertices tends to infinity with $m$; the construction produces graphs of every sufficiently large order.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L14713-L14733

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.hammingRetentionProbability_mul_wordCount_tendsto_atTop :
    Tendsto
      (fun dimension : ℕ =>
        hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ))
      atTop atTop := by sorry
