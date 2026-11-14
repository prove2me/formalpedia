-- Prove2me | Theorems.Thm_ConsistentSubmodular_Chains_IsDescendingChain_skip
-- name    : ConsistentSubmodular.Chains.IsDescendingChain.skip
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:14.179999+00:00
-- url     : https://prove2.me/theorems/b091131b-3222-445d-b73a-3f861312621b
-- title:
--   Deleting the middle vertex of a descending chain keeps a chain
-- statement:
--   Call a list $L$ of reals a descending chain if it is weakly decreasing (each entry is at most its predecessor), all its entries are at least $1$, and its last entry is $1$. Let $x,y,z\in\mathbb R$ and let `rest` be a list of reals. If $(x,y,z,\text{rest})$ is a descending chain, then $(x,z,\text{rest})$ is also a descending chain.
--
--   This is the elementary closure property used when vertices that start a nonpositive edge are deleted from a chain, in the proof that every chain $d_0\ge\dots\ge d_N=1$ has value at most $q$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/ConsecutiveChains.lean#L509-L521 (`ConsistentSubmodular.Chains.IsDescendingChain.skip`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ConsecutiveChains

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains
variable {x y z : ℝ} {rest : List ℝ}

theorem ConsistentSubmodular.Chains.IsDescendingChain.skip (h : IsDescendingChain (x :: y :: z :: rest)) : IsDescendingChain (x :: z :: rest) := by sorry
