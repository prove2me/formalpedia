-- Prove2me | Theorems.Thm_ConstantWeightCode_A_30_10_9_ge_210
-- name    : ConstantWeightCode.A_30_10_9_ge_210
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-25T04:59:29.824704+00:00
-- url     : https://prove2.me/theorems/b1b81898-1304-4ca5-83af-de7c1b95690c
-- title:
--   New lower bound $A(30,10,9)\ge 210$ for binary constant-weight codes
-- statement:
--   A **binary constant-weight code** with parameters $(n,d,w)$ is a set $C$ of binary words $x=(x_1,\dots,x_n)\in\{0,1\}^n$ such that
--
--   1. every word $x\in C$ has Hamming weight exactly $w$, i.e. $\mathrm{wt}(x)=|\{i : x_i=1\}|=w$, and
--   2. any two distinct words $x\neq y$ in $C$ have Hamming distance $d_H(x,y)=|\{i : x_i\neq y_i\}|\ge d$.
--
--   The number $A(n,d,w)$ is the largest possible size of such a code. This theorem asserts the lower bound
--
--   $$
--   A(30,10,9)\ \ge\ 210 .
--   $$
--
--   That is, there are $210$ binary words of length $30$, each having exactly nine coordinates equal to $1$, such that any two of them differ in at least ten coordinates. Equivalently, any two of the words have at most four positions of $1$ in common.
--
--   A. E. Brouwer maintains the standard table of lower bounds for $A(n,d,w)$. As of 2026-10-24 that table lists $A(30,10,9)\ge 203$, so this statement improves the best known lower bound by $7$. The code was found by a computer search, and an explicit list of its $210$ codewords is part of the proof.
--
--   **Formalization Note** A word is a function `Fin 30 → Bool`, with `true` standing for the symbol $1$. Its weight is the number of coordinates whose value is `true`, and the distance between two words is Mathlib's `hammingDist`. The code is a `Finset` of exactly $210$ such words.
-- source:
--   A. E. Brouwer, table of lower bounds for binary constant weight codes A(n,d,w), https://aeb.win.tue.nl/codes/Andw.html, entry n = 30, d = 10, w = 9: best known lower bound 203 as of 2026-10-24. The size-210 code was found by computer search and is given explicitly in the proof.

import Mathlib

theorem ConstantWeightCode.A_30_10_9_ge_210 : ∃ C : Finset (Fin 30 → Bool), C.card = 210 ∧ (∀ x ∈ C, (Finset.univ.filter (fun i => x i = true)).card = 9) ∧ (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 10 ≤ hammingDist x y) := by sorry
