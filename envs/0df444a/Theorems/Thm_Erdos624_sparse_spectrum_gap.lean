-- Prove2me | Theorems.Thm_Erdos624_sparse_spectrum_gap
-- name    : Erdos624.sparse_spectrum_gap
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T19:35:57.49941+00:00
-- url     : https://prove2.me/theorems/d500093c-95b4-4a3e-aeb0-d012853d80cc
-- title:
--   Sparse-spectrum gap: low-weight words form a subspace with support $\le2K$ (Erdős 624)
-- statement:
--   Let $Q\le\mathbb F_2^U$ ($U$ finite), with weight $\operatorname{wt}(f)=|\{x:f(x)\ne0\}|$, and integers with $2K\le a$ such that every $f\in Q$ with $\operatorname{wt}f\le a$ has $\operatorname{wt}f\le K$. Let $F=\{f\in Q:\operatorname{wt}f\le a\}$. **Theorem.** (i) $F$ is closed under addition (so it is a subspace), with weights $\le K$. (ii) Any set $T$ of coordinates on each of which some word of $F$ is nonzero has $|T|\le2K$; in particular the support $T_u$ of $F$ has $|T_u|\le 2K$. (iii) Every $g\in Q$ supported inside $T_u$ lies in $F$ (weight $\le K$), so $F=Q\cap\mathbb F_2^{T_u}$.
--
--   Source: 'Sparse Parity Localization from Actual Repairs', (S) and (K).
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. The notes study a hypothetical two-track counterexample: $n=2^k$, colour lists $L(A)$ of size at most two on inputs $A$, and every $k$-set attaining every colour. This is an auxiliary finite statement from Sol's Round 14 notes. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 14: Sol's Perplexity Computer notes (best dense cores, lower-layer forcing, near-saturation, witness backbone, joint exterior budget, core hubs, sparse parity) (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem sparse_spectrum_gap {U : Type*} [Fintype U] [DecidableEq U] (Q : Submodule (ZMod 2) (U → ZMod 2))
    (a K : ℕ) (hK : 2 * K ≤ a)
    (hgap : ∀ f ∈ Q, #(univ.filter (fun x => f x ≠ 0)) ≤ a →
      #(univ.filter (fun x => f x ≠ 0)) ≤ K) :
    (∀ f ∈ Q, ∀ g ∈ Q, #(univ.filter (fun x => f x ≠ 0)) ≤ a →
      #(univ.filter (fun x => g x ≠ 0)) ≤ a → #(univ.filter (fun x => (f + g) x ≠ 0)) ≤ K) ∧
    (∀ T : Finset U, (∀ x ∈ T, ∃ f ∈ Q, #(univ.filter (fun y => f y ≠ 0)) ≤ a ∧ f x ≠ 0) →
      #T ≤ 2 * K) ∧
    (∀ g ∈ Q, (∀ x, g x ≠ 0 → ∃ f ∈ Q, #(univ.filter (fun y => f y ≠ 0)) ≤ a ∧ f x ≠ 0) →
      #(univ.filter (fun x => g x ≠ 0)) ≤ K) := by sorry

end Erdos624
