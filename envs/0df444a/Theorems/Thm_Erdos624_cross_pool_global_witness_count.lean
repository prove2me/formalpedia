-- Prove2me | Theorems.Thm_Erdos624_cross_pool_global_witness_count
-- name    : Erdos624.cross_pool_global_witness_count
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T20:29:50.805131+00:00
-- url     : https://prove2.me/theorems/8ca03a51-777f-495e-b876-8c78a531946c
-- title:
--   Cross-pool witness accounting (OFF)+(GLOBAL): no long-input reuse across compressed pools (Erdős 624)
-- statement:
--   $C$ is a palette with $|C|=n=2^k$, $L$ assigns to each input $A$ a list $L(A)\subseteq C$ with $|L(A)|\le2$ (the empty input included; $b_0=|L(\varnothing)|$). Let $(W_i)_{i\in I}$ be pools with $|W_i\cap W_h|\le R$ for $i\ne h$ (OVERLAP). For each $i$ let $\mathcal S_i$ be a set of colours, and for $u\in\mathcal S_i$ fix a preferred size $a_{u,i}$ and a raw covering core $\mathcal G_{u,i}\subseteq\mathcal P(W_i)$ (inputs carrying $u$, meeting every $k$-face of $W_i$). Assume each $u\in\mathcal S_i$ has no short inputs in $W_i$ (no input $A\subseteq W_i$ with $|A|\le R$ carries $u$, including $\varnothing$) and is robustly mixed at its preferred size (for every $P\subseteq W_i$ with $|P|\ge|W_i|-s$ some $k$-face of $P$ contains no $a_{u,i}$-input carrying $u$). Let $\mathcal O_{u,i}=\{A\in\mathcal G_{u,i}:|A|\ne a_{u,i}\}$. **Theorem (GLOBAL).** $$(s+1)\sum_i|\mathcal S_i|\le2\Bigl|\bigcup_i\bigcup_{u\in\mathcal S_i}\mathcal O_{u,i}\Bigr|.$$
--
--   Source: 'Polynomial Subpools and Cross-Pool Witness Accounting', (OFF) and (GLOBAL).
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. The notes study a hypothetical two-track counterexample: $n=2^k$, colour lists $L(A)$ of size at most two on inputs $A$, and every $k$-set attaining every colour. This is an auxiliary finite statement from Sol's Round 14/15 notes. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 15: Sol's Perplexity Computer notes 'Unrooted Coverage Forces Mixed-Layer Cores' and 'Polynomial Subpools and Cross-Pool Witness Accounting' (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem cross_pool_global_witness_count {U : Type*} [DecidableEq U] {C : Type*} [DecidableEq C]
    {ι : Type*} [DecidableEq ι]
    (L : Finset U → Finset C) (hb : ∀ A, #(L A) ≤ 2) (k R s : ℕ) (I : Finset ι)
    (W : ι → Finset U) (hW : ∀ i ∈ I, ∀ h ∈ I, i ≠ h → #(W i ∩ W h) ≤ R)
    (S : ι → Finset C) (G : ι → C → Finset (Finset U)) (a : ι → C → ℕ)
    (hS : ∀ i ∈ I, ∀ u ∈ S i,
      (∀ A ⊆ W i, #A ≤ R → u ∉ L A) ∧
      (∀ P ⊆ W i, #(W i) ≤ #P + s → ∃ Y ⊆ P, #Y = k ∧ ∀ A ⊆ Y, #A = a i u → u ∉ L A) ∧
      G i u ⊆ (W i).powerset ∧ (∀ A ∈ G i u, u ∈ L A) ∧
      (∀ Y ⊆ W i, #Y = k → ∃ A ∈ G i u, A ⊆ Y)) :
    (s + 1) * ∑ i ∈ I, #(S i) ≤
      2 * #(I.biUnion fun i => (S i).biUnion fun u => (G i u).filter (fun A => #A ≠ a i u)) := by sorry

end Erdos624
