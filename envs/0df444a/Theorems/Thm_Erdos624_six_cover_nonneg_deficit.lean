-- Prove2me | Theorems.Thm_Erdos624_six_cover_nonneg_deficit
-- name    : Erdos624.six_cover_nonneg_deficit
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-18T10:25:42.755755+00:00
-- url     : https://prove2.me/theorems/2fc783f1-9f57-42e1-87a2-6a8ac5702bdd
-- title:
--   Nonnegative deficit of an intersecting six-cover (Erdős 624)
-- statement:
--   Let $Z$ be a finite set with $|Z|\ge 2$, and let $S$ be a family of exactly six nonempty subsets of $Z$. Suppose that no two distinct members of $S$ are disjoint, and that every $Y\subseteq Z$ with $|Y|=|Z|-2$ contains some member of $S$. (When $|Z|=k+2$, these $Y$ are the $k$-faces of $Z$.) Write $d(z)=\#\{A\in S:z\in A\}$. Then $d(z)\le 3$ for every $z\in Z$, and $\sum_{A\in S}|A|\le 3|Z|$, with equality if and only if $d(z)=3$ for every $z\in Z$. Equivalently, the deficit $\Delta(S)=3|Z|-\sum_{A\in S}|A|=\sum_{z\in Z}(3-d(z))$ is nonnegative, and vanishes precisely on exact $3$-regular sixes.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$. This is an auxiliary finite combinatorial statement from Sol's 2026-11-17/18 notes (relayed by Ethan Cheung). It does **not** settle Erdős Problem 624, PAIR, Step 17, or DENSE-P.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 19: official-def formalization of finite lemmas from GPT 6.1 Sol's analysis, relayed by Ethan Cheung (three-cell criterion in the 2026-11-18 pasted note; deficit identity in Transfer Prompt on Zero-Deficit Six-Covers, task d32c2107-b546-4015-be2e-c9c4e46ce7cd); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Nov 18 2026). Auxiliary finite results only; do NOT settle PAIR / Step 17 / DENSE-P / #624.

import Mathlib
open Finset Function

namespace Erdos624

theorem six_cover_nonneg_deficit {U : Type*} [DecidableEq U]
    (Z : Finset U) (S : Finset (Finset U))
    (hZ : 2 ≤ #Z)
    (hS : #S = 6)
    (hsub : ∀ A ∈ S, A ⊆ Z)
    (hne : ∀ A ∈ S, A.Nonempty)
    (hnd : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → ¬ Disjoint A B)
    (hcov : ∀ Y ⊆ Z, #Y = #Z - 2 → ∃ A ∈ S, A ⊆ Y) :
    (∀ z ∈ Z, #{A ∈ S | z ∈ A} ≤ 3) ∧
    ∑ A ∈ S, #A ≤ 3 * #Z ∧
    (∑ A ∈ S, #A = 3 * #Z ↔ ∀ z ∈ Z, #{A ∈ S | z ∈ A} = 3) := by sorry

end Erdos624
