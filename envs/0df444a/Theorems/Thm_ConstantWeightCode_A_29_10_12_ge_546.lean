-- Prove2me | Theorems.Thm_ConstantWeightCode_A_29_10_12_ge_546
-- name    : ConstantWeightCode.A_29_10_12_ge_546
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-05T16:11:45.999435+00:00
-- url     : https://prove2.me/theorems/469536cc-ebd7-4232-9b46-b05ce3cb89f1
-- title:
--   New lower bound $A(29,10,12)\ge 546$ for binary constant-weight codes
-- statement:
--   A **binary constant-weight code** with parameters $(n,d,w)$ is a set $C$ of binary words $x=(x_1,\dots,x_n)\in\{0,1\}^n$ such that
--
--   1. every word $x\in C$ has Hamming weight exactly $w$, i.e. $\mathrm{wt}(x)=|\{i : x_i=1\}|=w$, and
--   2. any two distinct words $x\neq y$ in $C$ have Hamming distance $d_H(x,y)=|\{i : x_i\neq y_i\}|\ge d$.
--
--   The number $A(n,d,w)$ is the largest possible size of such a code. This theorem asserts the lower bound
--
--   $$
--   A(29,10,12)\ \ge\ 546 .
--   $$
--
--   That is, there are $546$ binary words of length $29$, each having exactly twelve coordinates equal to $1$, such that any two of them differ in at least ten coordinates. Equivalently, any two of the words have at most seven positions of $1$ in common.
--
--   A. E. Brouwer maintains the standard table of lower bounds for $A(n,d,w)$. As of 2026-11-05 that table lists $A(29,10,12)\ge 543$, so this statement improves the best known lower bound by $3$. The code was found by a computer search, and an explicit list of its $546$ codewords is part of the proof.
--
--   **Formalization Note** A word is a function `Fin 29 → Bool`, with `true` standing for the symbol $1$. Its weight is the number of coordinates whose value is `true`, and the distance between two words is Mathlib's `hammingDist`. The code is a `Finset` of exactly $546$ such words.
-- source:
--   A. E. Brouwer, table of lower bounds for binary constant weight codes A(n,d,w), https://aeb.win.tue.nl/codes/Andw.html, entry n = 29, d = 10, w = 12: best known lower bound 543 as of 2026-11-05. The size-546 code was found by computer search and is given explicitly in the proof.

import Mathlib

theorem ConstantWeightCode.A_29_10_12_ge_546 : ∃ C : Finset (Fin 29 → Bool), C.card = 546 ∧ (∀ x ∈ C, (Finset.univ.filter (fun i => x i = true)).card = 12) ∧ (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 10 ≤ hammingDist x y) := by sorry
