-- Prove2me | Theorems.Thm_Erdos624_odd_subsets_span_parity_space
-- name    : Erdos624.odd_subsets_span_parity_space
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T20:10:35.417495+00:00
-- url     : https://prove2.me/theorems/82cdafb1-bf3c-41c8-a35e-0ca9d9ebf0f3
-- title:
--   Odd $k$: the $k$-subsets of a $(\ge k+1)$-set span $\mathbb F_2^Q$ (Erdős 624)
-- statement:
--   **Theorem.** Let $k$ be odd and $Q$ a finite set with $|Q|\ge k+1$. Then the indicator vectors $\mathbf 1_Y$ of the $k$-subsets $Y\subseteq Q$ span the whole space $\mathbb F_2^Q$: every $f:U\to\mathbb F_2$ supported in $Q$ is an $\mathbb F_2$-combination of them.
--
--   Source: 'Best Dense Cores and Mandatory Mixed-Face Obstructions', finite core of the DENSE-COLLAPSE construction (k odd).
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. The notes study a hypothetical two-track counterexample: $n=2^k$, colour lists $L(A)$ of size at most two on inputs $A$, and every $k$-set attaining every colour. This is an auxiliary finite statement from Sol's Round 14/15 notes. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 15: Sol's Perplexity Computer notes (outside coverage / core erasure, best dense cores, near-saturation, witness backbone, supported-loss localization, unrooted mixed-layer cores, polynomial subpools) (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem odd_subsets_span_parity_space {U : Type*} [DecidableEq U] (k : ℕ) (hk : Odd k) (Q : Finset U)
    (hQ : k + 1 ≤ #Q) (f : U → ZMod 2) (hf : ∀ y, f y ≠ 0 → y ∈ Q) :
    f ∈ Submodule.span (ZMod 2)
      {g | ∃ Y ⊆ Q, #Y = k ∧ g = fun y => if y ∈ Y then (1 : ZMod 2) else 0} := by sorry

end Erdos624
