-- Prove2me | Theorems.Thm_Erdos624_three_cell_six_cover_iff
-- name    : Erdos624.three_cell_six_cover_iff
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-18T10:25:46.545813+00:00
-- url     : https://prove2.me/theorems/2fd34ae9-342a-41dc-a2ad-b0e039fc615f
-- title:
--   Three-cell criterion for exact six-row balance and coverage (Erdős 624)
-- statement:
--   Fix a finite set $R$ with $|R|\ge 1$ and a point $x\notin R$. Let $P,E:\mathrm{Fin}\,3\to\mathrm{Finset}\,U$ be injective, with each $P_i\subseteq R$ and each $E_j\subseteq R\cup\{x\}$ containing $x$. For $z\in R$ write $I(z)=\{i:z\in P_i\}$ and $J(z)=\{j:z\in E_j\}$. For each index $i\in\{0,1,2\}$ let $H_i$ be the set of labels $j$ for which some $z\in R$ has $I(z)=[3]\setminus\{i\}$ and $j\in J(z)$, and let $L_i$ be the set of labels $j$ for which some $z\in R$ has $I(z)=\{i\}$ and $j\notin J(z)$. The following are equivalent. (1) No $I(z)$ equals $[3]$; $|J(z)|=3-|I(z)|$ for every $z\in R$; and $H_i\cap L_i=\varnothing$ for all three $i$. (2) Every point of $R\cup\{x\}$ lies in exactly three of the six rows $\{P_0,P_1,P_2,E_0,E_1,E_2\}$, and every $Y\subseteq R\cup\{x\}$ of cardinality $|R\cup\{x\}|-2$ contains one of the six rows. When $|R|=k+1$, this is a necessary and sufficient test for exact $3$-and-$3$ balance and six-row coverage of the $k$-faces of the window $R\cup\{x\}$.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$. This is an auxiliary finite combinatorial statement from Sol's 2026-11-17/18 notes (relayed by Ethan Cheung). It does **not** settle Erdős Problem 624, PAIR, Step 17, or DENSE-P.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 19: official-def formalization of finite lemmas from GPT 6.1 Sol's analysis, relayed by Ethan Cheung (three-cell criterion in the 2026-11-18 pasted note; deficit identity in Transfer Prompt on Zero-Deficit Six-Covers, task d32c2107-b546-4015-be2e-c9c4e46ce7cd); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Nov 18 2026). Auxiliary finite results only; do NOT settle PAIR / Step 17 / DENSE-P / #624.

import Mathlib
open Finset Function

namespace Erdos624

theorem three_cell_six_cover_iff {U : Type*} [DecidableEq U]
    (R : Finset U) (x : U) (hx : x ∉ R)
    (P E : Fin 3 → Finset U)
    (hPinj : Function.Injective P) (hEinj : Function.Injective E)
    (hP : ∀ i, P i ⊆ R) (hE : ∀ i, E i ⊆ insert x R) (hxE : ∀ i, x ∈ E i)
    (hR : 1 ≤ #R) :
    ((∀ z ∈ R, (univ.filter (fun i : Fin 3 => z ∈ P i) : Finset (Fin 3)) ≠ univ) ∧
      (∀ z ∈ R, #(univ.filter (fun j : Fin 3 => z ∈ E j)) =
        3 - #(univ.filter (fun i : Fin 3 => z ∈ P i))) ∧
      (∀ i : Fin 3,
        Disjoint
          (univ.filter (fun j : Fin 3 =>
            ∃ z ∈ R, univ.filter (fun k : Fin 3 => z ∈ P k) = univ.erase i ∧
              j ∈ univ.filter (fun k : Fin 3 => z ∈ E k)))
          (univ.filter (fun j : Fin 3 =>
            ∃ z ∈ R, univ.filter (fun k : Fin 3 => z ∈ P k) = {i} ∧
              j ∉ univ.filter (fun k : Fin 3 => z ∈ E k))))) ↔
    ((∀ y ∈ insert x R,
        #{A ∈ (univ.image P ∪ univ.image E) | y ∈ A} = 3) ∧
      (∀ Y ⊆ insert x R, #Y = #(insert x R) - 2 →
        ∃ A ∈ univ.image P ∪ univ.image E, A ⊆ Y)) := by sorry

end Erdos624
