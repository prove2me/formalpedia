-- Prove2me | Theorems.Thm_Erdos146_hammingHost_adj_iff
-- name    : Erdos146.hammingHost_adj_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:50:08.474055+00:00
-- url     : https://prove2.me/theorems/10aa1458-5892-442f-974a-1eab17e60c30
-- title:
--   Adjacency in the Hamming-ball host
-- statement:
--   Supporting fact for the sampled Hamming-ball graph of Section 7. The host is the sampled Hamming-ball graph of Section 7: with $U = \{0,1\}^m$, two disjoint copies $U_L, U_R$ are joined whenever their Hamming distance is at most $k = \lfloor \tau m \rfloor$, and each vertex is retained independently with probability $p = 2^{-\beta m}$. Two vertices on opposite sides are adjacent exactly when their Hamming distance is at most $k = \lfloor \tau m\rfloor$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L15963-L15976

import Definitions.Def_erdos146_core2
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.InformationTheory.Hamming

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.hammingHost_adj_iff (dimension radius : ℕ)
    (x y : Bool × HammingWord dimension) :
    (hammingHost dimension radius).Adj x y ↔
      x.1 ≠ y.1 ∧ hammingDist x.2 y.2 ≤ radius := by sorry
