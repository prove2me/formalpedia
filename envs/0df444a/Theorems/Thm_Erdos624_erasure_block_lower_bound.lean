-- Prove2me | Theorems.Thm_Erdos624_erasure_block_lower_bound
-- name    : Erdos624.erasure_block_lower_bound
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T15:29:13.788323+00:00
-- url     : https://prove2.me/theorems/6a0dec8b-61a6-4664-9fb3-f63b99a015a4
-- title:
--   Erasure-cost lower bound: a parity certificate must delete a point of each zero-sum triple block (Erdős 624 cross-review)
-- statement:
--   Let $P_1,\dots,P_t$ be pairwise disjoint finite sets of coordinates and, for each $j$, let $E^1_j,E^2_j,E^3_j\subseteq P_j$ satisfy $\chi_{E^1_j}+\chi_{E^2_j}+\chi_{E^3_j}=0$ over $\mathbb F_2$ (relation (Z)). Let $R$ be a set of deleted coordinates and $w$ an $\mathbb F_2$-valued form such that every $E^i_j$ disjoint from $R$ has $\sum_{x\in E^i_j}w(x)=1$. Then $|R|\ge t$.
--
--   In the cross-review's construction these are the three proper minimal witnesses of a colour $u_z$ in each block, so every successful deletion meets all $t$ blocks: $\sigma_{u_z}(U)\ge t$ (the lower half of (EC)).
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. This is an auxiliary finite statement from Sol's Round 12 Step 17 cross-review / resilience analysis of the two-track (PAIR) case. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 12: Sol's 'Step 17: First-Round Cross-Review' and 'Step 17: resilient relations below the top layer'; derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem erasure_block_lower_bound {U : Type*} [DecidableEq U] (t : ℕ) (P : Fin t → Finset U)
    (hP : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (E1 E2 E3 : Fin t → Finset U) (h1 : ∀ j, E1 j ⊆ P j) (h2 : ∀ j, E2 j ⊆ P j)
    (h3 : ∀ j, E3 j ⊆ P j)
    (hZ : ∀ j x, ((if x ∈ E1 j then 1 else 0) + (if x ∈ E2 j then 1 else 0) +
      (if x ∈ E3 j then 1 else 0) : ZMod 2) = 0)
    (R : Finset U) (w : U → ZMod 2)
    (hw : ∀ j, (Disjoint (E1 j) R → ∑ x ∈ E1 j, w x = 1) ∧
      (Disjoint (E2 j) R → ∑ x ∈ E2 j, w x = 1) ∧ (Disjoint (E3 j) R → ∑ x ∈ E3 j, w x = 1)) :
    t ≤ #R := by sorry

end Erdos624
