-- Prove2me | Theorems.Thm_Erdos624_seven_row_omission_iff
-- name    : Erdos624.seven_row_omission_iff
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-19T15:08:35.450181+00:00
-- url     : https://prove2.me/theorems/06aad9ee-103e-49c6-84ba-b1e3c00eeb78
-- title:
--   Exact omission test for a seven-row window (Erdős 624)
-- statement:
--   Let $Z$ be a finite set with $|Z|\ge 2$, and let $T$ be a family of exactly seven subsets of $Z$. Write $D(z)=\#\{A\in T:z\in A\}$ and $S=\{z\in Z:D(z)=4\}$. The following are equivalent. (1) There is a member $R\in T$ such that every $Y\subseteq Z$ with $|Y|=|Z|-2$ contains some member of $T\setminus\{R\}$, and every point of $Z$ lies in exactly three members of $T\setminus\{R\}$. (2) $D(z)\in\{3,4\}$ for every $z\in Z$, the set $S$ itself belongs to $T$, and every $Y\subseteq Z$ with $|Y|=|Z|-2$ contains some member of $T\setminus\{S\}$. Thus the only row that can be omitted to leave a three-regular cover is the degree-four set $S$, and then only if $S$ is one of the seven raw rows and the remaining six still cover.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$. This is an auxiliary finite combinatorial statement from GPT-6.2-Astra's 2026-11-19 analysis (relayed by Ethan Cheung). It does **not** settle Erdős Problem 624, PAIR, Step 17, or DENSE-P, and it does **not** prove a positive density of zero-deficit six-covers.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 20: official-def formalization of finite lemmas from GPT-6.2-Astra's analysis, relayed by Ethan Cheung (public thread https://poe.com/s/uJXfxBGozGrNfWyhQ3XO, later messages on zero-deficit six-covers, 2026-11-19); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (19 Nov 2026, Asia/Hong_Kong). Auxiliary finite results only; do NOT settle PAIR / Step 17 / DENSE-P / #624.

import Mathlib
open Finset Function

namespace Erdos624

theorem seven_row_omission_iff {U : Type*} [DecidableEq U]
    (Z : Finset U) (T : Finset (Finset U))
    (hZ : 2 ≤ #Z)
    (hT : #T = 7)
    (hsub : ∀ A ∈ T, A ⊆ Z) :
    (∃ R ∈ T,
        (∀ Y ⊆ Z, #Y = #Z - 2 → ∃ A ∈ T.erase R, A ⊆ Y) ∧
        (∀ z ∈ Z, #{A ∈ T.erase R | z ∈ A} = 3)) ↔
      ((∀ z ∈ Z, #{A ∈ T | z ∈ A} = 3 ∨ #{A ∈ T | z ∈ A} = 4) ∧
        (Z.filter (fun z => #{A ∈ T | z ∈ A} = 4) ∈ T) ∧
        (∀ Y ⊆ Z, #Y = #Z - 2 →
          ∃ A ∈ T.erase (Z.filter (fun z => #{A ∈ T | z ∈ A} = 4)), A ⊆ Y)) := by sorry

end Erdos624
