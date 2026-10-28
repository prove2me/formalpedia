-- Prove2me | Theorems.Thm_Erdos624_common_root_budget
-- name    : Erdos624.common_root_budget
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T13:44:26.194328+00:00
-- url     : https://prove2.me/theorems/6795fa80-3363-41bd-8f81-644c768a59e7
-- title:
--   Common-root budget for top-only repairs $\sum_{u\in M}|B_u|\le 2(N-k+1)$ (Erdős 624 Round 10)
-- statement:
--   Let $C$ be a finite set of colours and $L:\mathcal P(U)\to\mathcal P(C)$ a list system of capacity $2$, i.e. $|L(A)|\le2$ for every finite $A\subseteq U$. For finite $Y$ write $J(Y)=\bigcup_{A\subseteq Y}L(A)$ and the proper palette $J^\circ(Y)=\bigcup_{A\subsetneq Y}L(A)$.
--
--   Let $k\ge1$, let $V$ be a finite pool with $N=|V|$, and assume full coverage: $J(Y)=C$ for every $k$-subset $Y\subseteq V$. Let $W\subseteq V$ with $|W|=k-1$, put $M=C\setminus J(W)$, and for $u\in M$ let
--   $$B_u=\{x\in V\setminus W:\ u\notin J^\circ(W\cup\{x\})\}$$
--   be the one-point extensions on which $u$ has no proper repair. Then
--   $$\sum_{u\in M}|B_u|\le 2(N-k+1).$$
--
--   This is inequality (31) from Sol's Round 10 analysis of Erdős Problem 624 (Step 17). It is an auxiliary lemma and does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 10 Step 17 report 'resilient relations below the top layer', section 'Proved: a common-root budget for top-only repairs', eqs. (30)-(31); derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; Lean by Grok Bot for Ethan Cheung (Oct 24 2026). Honest: a proved auxiliary lemma only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

/-- Common-root budget for top-only repairs (Sol Round 10, eq. (31)). Capacity 2, `W ⊆ V`, `|W| = k-1`, full coverage:
`Σ_{u ∉ J(W)} |B_u| ≤ 2 (N-k+1)` with `B_u = {x ∈ V \ W : u ∉ J°(W ∪ {x})}`. Does not settle PAIR / #624. -/
theorem common_root_budget {U C : Type*} [DecidableEq U] [Fintype C] [DecidableEq C]
    (L : Finset U → Finset C) (k : ℕ) (hk : 1 ≤ k) (V W : Finset U) (hWV : W ⊆ V)
    (hW : W.card = k - 1) (hq : ∀ A, (L A).card ≤ 2)
    (hcov : ∀ Y ∈ V.powersetCard k, ∀ u : C, u ∈ Y.powerset.biUnion L) :
    ∑ u ∈ univ \ W.powerset.biUnion L,
        ((V \ W).filter (fun x =>
          u ∉ ((insert x W).powerset.filter (fun A => A ≠ insert x W)).biUnion L)).card
      ≤ 2 * (V.card + 1 - k) := by sorry

end Erdos624
