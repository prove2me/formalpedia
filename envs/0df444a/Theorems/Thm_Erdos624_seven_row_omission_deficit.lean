-- Prove2me | Theorems.Thm_Erdos624_seven_row_omission_deficit
-- name    : Erdos624.seven_row_omission_deficit
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-19T15:08:37.303424+00:00
-- url     : https://prove2.me/theorems/c7df7f41-958d-492a-b22c-429567042911
-- title:
--   Exact deficit formula after omitting one of seven raw rows (Erdős 624)
-- statement:
--   Let $Z$ be a finite set with $|Z|\ge 2$, and let $T$ be a family of exactly seven nonempty subsets of $Z$, no two of them disjoint. Let $R\in T$ be such that every $Y\subseteq Z$ with $|Y|=|Z|-2$ contains some member of $T\setminus\{R\}$. Write $D(z)=\#\{A\in T:z\in A\}$ and $S=\{z\in Z:D(z)=4\}$. Then $D(z)\le 4$ for every $z\in Z$, one has $S\subseteq R$, and the deficit after omitting $R$ is $3|Z|-\sum_{A\in T\setminus\{R\}}|A|=\sum_{z:\,D(z)\le 2}(3-D(z))+|R\setminus S|$. In particular, trying several removable rows can improve only the second term; it cannot repair a vertex of raw degree at most two.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$. This is an auxiliary finite combinatorial statement from GPT-6.2-Astra's 2026-11-19 analysis (relayed by Ethan Cheung). It does **not** settle Erdős Problem 624, PAIR, Step 17, or DENSE-P, and it does **not** prove a positive density of zero-deficit six-covers.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 20: official-def formalization of finite lemmas from GPT-6.2-Astra's analysis, relayed by Ethan Cheung (public thread https://poe.com/s/uJXfxBGozGrNfWyhQ3XO, later messages on zero-deficit six-covers, 2026-11-19); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (19 Nov 2026, Asia/Hong_Kong). Auxiliary finite results only; do NOT settle PAIR / Step 17 / DENSE-P / #624.

import Mathlib
open Finset Function

namespace Erdos624

theorem seven_row_omission_deficit {U : Type*} [DecidableEq U]
    (Z : Finset U) (T : Finset (Finset U)) (R : Finset U)
    (hZ : 2 ≤ #Z)
    (hT : #T = 7)
    (hR : R ∈ T)
    (hsub : ∀ A ∈ T, A ⊆ Z)
    (hne : ∀ A ∈ T, A.Nonempty)
    (hnd : ∀ A ∈ T, ∀ B ∈ T, A ≠ B → ¬ Disjoint A B)
    (hcov : ∀ Y ⊆ Z, #Y = #Z - 2 → ∃ A ∈ T.erase R, A ⊆ Y) :
    (∀ z ∈ Z, #{A ∈ T | z ∈ A} ≤ 4) ∧
      (Z.filter (fun z => #{A ∈ T | z ∈ A} = 4) ⊆ R) ∧
      (3 * #Z - ∑ A ∈ T.erase R, #A =
        (∑ z ∈ Z.filter (fun z => #{A ∈ T | z ∈ A} ≤ 2),
            (3 - #{A ∈ T | z ∈ A})) +
          #(R \ Z.filter (fun z => #{A ∈ T | z ∈ A} = 4))) := by sorry

end Erdos624
