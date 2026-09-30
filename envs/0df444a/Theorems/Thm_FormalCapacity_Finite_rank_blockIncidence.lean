-- Prove2me | Theorems.Thm_FormalCapacity_Finite_rank_blockIncidence
-- name    : FormalCapacity.Finite.rank_blockIncidence
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-07T18:07:08.734063+00:00
-- url     : https://prove2.me/theorems/ae410fd5-7dc1-4142-9e32-e99be32e6b5f
-- title:
--   Exact rank of the full nonempty-block incidence projection
-- statement:
--   Let $X$ be a nonempty finite label set with $n=|X|$. Let $\mathcal B(X)$ be its nonempty subsets and $\Pi(X)$ its genuine set partitions. Over $\mathbb Q$, define $T$ by $(Tc)(P)=\sum_{B\in P}c_B$. Then
--
--   $$\dim_{\mathbb Q}\operatorname{range}T=2^n-n.$$
--
--   The formula measures how many independent additive block statistics remain after all partition identities are taken into account. It is a theorem for every nonempty finite label set, not only for four labels. The map is the transpose of the block-incidence projection from signed partition laws to block coordinates. The formal right-hand side uses natural-number subtraction; no claim is made for $n=0$.
-- source:
--   The four-label correlation threshold, Theorem 2.1, rank assertion in (2.2). Unpublished research note (2026), N4_BLOCK_CORRELATION_NOTE.md, SHA-256 a9b67c132ca0e0af807fb917ca2322833b84e162c45a4da7329ee88fbe4f1c83. Exact formal source: formal_capacity/FormalCapacity/Finite/BlockRank.lean, lines 166–185, declaration FormalCapacity.Finite.rank_blockIncidence, source-file SHA-256 0adb1c853d3a750450a8b0f6899884f5e03206466fc1f165f86e21e0849a29bc. Local source archive; no public repository URL or commit is asserted. Upload checked with Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Definitions.Def_capacityFinitePartitions
import Definitions.Def_capacityBlockIncidence

set_option autoImplicit false

/-!
# Rank of first-order block incidence

This file upgrades the row-relation characterization in `Partition.lean` to
the finite-dimensional rank formula `2^n - n`.
-/

open FormalCapacity.Finite

open scoped BigOperators
open Finset Module

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem FormalCapacity.Finite.rank_blockIncidence [Nonempty α] :
    finrank ℚ (blockIncidenceTranspose (α := α)).range =
      2 ^ Fintype.card α - Fintype.card α := by
  sorry
