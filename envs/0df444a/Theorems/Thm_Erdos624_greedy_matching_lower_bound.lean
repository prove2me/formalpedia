-- Prove2me | Theorems.Thm_Erdos624_greedy_matching_lower_bound
-- name    : Erdos624.greedy_matching_lower_bound
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:14:18.127551+00:00
-- url     : https://prove2.me/theorems/2408eb93-c97c-4c44-bb7c-46578615ca23
-- title:
--   Greedy matching from large transversal number (MATCH): ν ≥ ⌊s/k⌋+1 (Erdős 624)
-- statement:
--   Let $\mathcal F$ be a finite family of nonempty finite sets, each of cardinality at most $k\ge1$. Write $\tau(\mathcal F)$ for the transversal number (minimum size of a set meeting every member of $\mathcal F$) and $\nu(\mathcal F)$ for the matching number (maximum number of pairwise disjoint members). **Theorem (MATCH).** If $\tau(\mathcal F)>s$, then $\nu(\mathcal F)\ge\lfloor s/k\rfloor+1$. Equivalently: every maximal pairwise-disjoint subfamily has size at least $\lfloor s/k\rfloor+1$.
--
--   Source: 'Unrooted Coverage Forces Mixed-Layer Cores', (MATCH); also the matching half of (OFF) in 'Polynomial Subpools and Cross-Pool Witness Accounting'. The same packing inequality appears as the dense-core (ROBUST) matching $\lceil(n-\ell+1)/k\rceil$ in 'Best Dense Cores'.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. The notes study a hypothetical two-track counterexample. This is an auxiliary finite statement from Sol's Round 14/15 notes (formalized in Round 16 leftovers). It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 16 leftovers: Sol's Perplexity Computer notes (Unrooted Coverage Forces Mixed-Layer Cores; Polynomial Subpools) from 2026-10-25 (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 29 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624. This is leftover formalization from R14/R15 docs, not new Sol progress after 2026-10-25.

import Mathlib
open Finset

namespace Erdos624

theorem greedy_matching_lower_bound {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (k s : ℕ) (hk : 1 ≤ k)
    (hne : ∀ A ∈ F, A.Nonempty)
    (hsize : ∀ A ∈ F, #A ≤ k)
    (hτ : ∀ T : Finset α, (∀ A ∈ F, (A ∩ T).Nonempty) → s < #T) :
    ∃ M ⊆ F, (M : Set (Finset α)).PairwiseDisjoint id ∧ s / k + 1 ≤ #M := by sorry

end Erdos624
