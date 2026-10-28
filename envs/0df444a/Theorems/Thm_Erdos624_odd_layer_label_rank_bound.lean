-- Prove2me | Theorems.Thm_Erdos624_odd_layer_label_rank_bound
-- name    : Erdos624.odd_layer_label_rank_bound
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T19:36:00.167511+00:00
-- url     : https://prove2.me/theorems/5a2a8faf-2f5c-409a-b6c4-e8a4c2ee7d31
-- title:
--   Odd central-layer label bound: at most $2(k-1)$ nonzero labels and rank $\le k-j$ (Erdős 624)
-- statement:
--   Let $q:U\to\mathbb F_2^r$ be coordinate labels (the evaluation functionals of a valid space), $P\subseteq U$, $j\le k$ with $j$ odd, and suppose every $k$-subset $Y\subseteq P$ contains a $j$-set $A$ with $\sum_{x\in A}q(x)=0$. **Theorem.** (i) At most $2(k-1)$ points of $P$ have $q(x)\neq0$. (ii) If $|P|\ge2k+j-3$ then $\dim\operatorname{span}q(P)\le k-j$.
--
--   Source: 'Best Dense Cores and Mandatory Mixed-Face Obstructions', central-layer individual losses (valid rank $\le k-j$, so $\beta\ge j-1$). The same lemma is the (BLOCK) step of 'Central-Layer Saturation'.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. The notes study a hypothetical two-track counterexample: $n=2^k$, colour lists $L(A)$ of size at most two on inputs $A$, and every $k$-set attaining every colour. This is an auxiliary finite statement from Sol's Round 14 notes. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 14: Sol's Perplexity Computer notes (best dense cores, lower-layer forcing, near-saturation, witness backbone, joint exterior budget, core hubs, sparse parity) (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem odd_layer_label_rank_bound {U : Type*} [Fintype U] [DecidableEq U] (r k j : ℕ) (hj : Odd j)
    (hjk : j ≤ k) (q : U → (Fin r → ZMod 2)) (P : Finset U)
    (hcov : ∀ Y ⊆ P, #Y = k → ∃ A ⊆ Y, #A = j ∧ ∑ x ∈ A, q x = 0) :
    #(P.filter (fun x => q x ≠ 0)) ≤ 2 * (k - 1) ∧
    (2 * k + j - 3 ≤ #P →
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (q '' (P : Set U))) + j ≤ k) := by sorry

end Erdos624
