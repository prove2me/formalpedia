-- Prove2me | Theorems.Thm_Erdos624_minimal_witness_budget
-- name    : Erdos624.minimal_witness_budget
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T13:44:23.596416+00:00
-- url     : https://prove2.me/theorems/dcdc2d33-da2b-4759-8932-3adeba9bc585
-- title:
--   Minimal-witness counting budget $|S|K\le qB_s(k)K+L_s\sum_u m_u^{>s}$ (Erdős 624 Round 10)
-- statement:
--   Let $U$ be a finite set with $|U|=n$, let $C$ be a set of colours, and let $L:\mathcal P(U)\to\mathcal P(C)$ be a list system of capacity $q$, i.e. $|L(A)|\le q$ for every $A\subseteq U$. A *minimal witness* of a colour $u$ is a set $M\subseteq U$ with $u\in L(M)$ and $u\notin L(A)$ for every proper subset $A\subsetneq M$; let $m_u^{>s}$ be the number of minimal witnesses of $u$ of size greater than $s$.
--
--   Fix integers $0\le s<k$ and put
--   $$K=\binom nk,\qquad B_s(k)=\sum_{i=0}^{s}\binom ki,\qquad L_s=\binom{n-s-1}{k-s-1}.$$
--   If $S\subseteq C$ is a finite set of colours such that every $k$-subset $Y\subseteq U$ covers every $u\in S$ (some $A\subseteq Y$ has $u\in L(A)$), then
--   $$|S|\,K\le q\,B_s(k)\,K+L_s\sum_{u\in S}m_u^{>s}.$$
--   (Natural-number subtraction is used in $n-s-1$.)
--
--   This is the minimal-witness counting budget from Sol's Round 10 analysis of Erdős Problem 624. It is an auxiliary counting inequality and does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 10 consolidated report, section 'Proved: witness complexity, forks, and repair budgets' → 'Minimal-witness counting budget' (boxed inequality); derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; Lean by Grok Bot for Ethan Cheung (Oct 24 2026). Honest: a proved auxiliary lemma only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

/-- Minimal-witness counting budget (Sol Round 10). Capacity-`q` list system, `S` covered on every `k`-face, `s < k`:
`|S| K ≤ q B_s(k) K + L_s Σ_{u∈S} m_u^{>s}`. Does not settle PAIR / #624. -/
theorem minimal_witness_budget {U C : Type*} [Fintype U] [DecidableEq U] [DecidableEq C]
    (L : Finset U → Finset C) (q k s : ℕ) (hq : ∀ A, (L A).card ≤ q) (hs : s < k)
    (S : Finset C)
    (hcov : ∀ Y ∈ (univ : Finset U).powersetCard k, ∀ u ∈ S, ∃ A ⊆ Y, u ∈ L A) :
    S.card * (Fintype.card U).choose k
      ≤ q * (∑ i ∈ range (s + 1), k.choose i) * (Fintype.card U).choose k
        + (Fintype.card U - s - 1).choose (k - s - 1)
          * ∑ u ∈ S, ((univ : Finset (Finset U)).filter
              (fun M => u ∈ L M ∧ (∀ A ⊂ M, u ∉ L A) ∧ s < M.card)).card := by sorry

end Erdos624
