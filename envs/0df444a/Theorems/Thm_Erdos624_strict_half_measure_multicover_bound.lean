-- Prove2me | Theorems.Thm_Erdos624_strict_half_measure_multicover_bound
-- name    : Erdos624.strict_half_measure_multicover_bound
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T19:36:00.705253+00:00
-- url     : https://prove2.me/theorems/0bb0eddd-7adc-4a94-b559-848726434a0f
-- title:
--   Strict half-measure $(s,\lambda)$-multicover bound $t\ge(\lambda+1)2^s-1$ (Erdős 624)
-- statement:
--   Atoms form a finite set $X$ with weights $w(x)>0$; $W=\sum_{x\in X}w(x)$, and blocks $B_i$ ($i\in I$, repetitions allowed) have measure $\mu(B_i)=\sum_{x\in X\cap B_i}w(x)$. The family is an $(s,\lambda)$-cover if every $S\subseteq X$ with $|S|\le s$ lies in at least $\lambda$ blocks. **Theorem.** If $\lambda\ge1$, $2\mu(B_i)<W$ for all $i$, and the blocks form an $(s,\lambda)$-cover, then $(\lambda+1)2^s\le |I|+1$.
--
--   Source: 'A Locally Forced Witness Backbone' (robust weighted multicover lemma, exact strict case); for $\lambda=1$ this is the half-measure covering lemma of 'Integral Near-Saturation on the Unchanged Assignment'.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. The notes study a hypothetical two-track counterexample: $n=2^k$, colour lists $L(A)$ of size at most two on inputs $A$, and every $k$-set attaining every colour. This is an auxiliary finite statement from Sol's Round 14 notes. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 14: Sol's Perplexity Computer notes (best dense cores, lower-layer forcing, near-saturation, witness backbone, joint exterior budget, core hubs, sparse parity) (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem strict_half_measure_multicover_bound {α ι : Type*} [DecidableEq α] (w : α → ℝ) (lam s : ℕ) (hlam : 1 ≤ lam)
    (X : Finset α) (I : Finset ι) (B : ι → Finset α)
    (hw : ∀ x ∈ X, 0 < w x)
    (hmeas : ∀ i ∈ I, 2 * ∑ x ∈ X.filter (fun x => x ∈ B i), w x < ∑ x ∈ X, w x)
    (hcov : ∀ S ⊆ X, #S ≤ s → lam ≤ #(I.filter (fun i => S ⊆ B i))) :
    (lam + 1) * 2 ^ s ≤ #I + 1 := by sorry

end Erdos624
