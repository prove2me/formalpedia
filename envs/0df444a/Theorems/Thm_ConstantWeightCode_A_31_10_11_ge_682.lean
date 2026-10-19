-- Prove2me | Theorems.Thm_ConstantWeightCode_A_31_10_11_ge_682
-- name    : ConstantWeightCode.A_31_10_11_ge_682
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-16T14:24:25.015551+00:00
-- url     : https://prove2.me/theorems/ef034df1-ce2d-4aeb-9f4f-780534791460
-- title:
--   New lower bound $A(31,10,11)\ge 682$ for binary constant-weight codes
-- statement:
--   A **binary constant-weight code** with parameters $(n,d,w)$ is a set $C$ of binary words $x=(x_1,\dots,x_n)\in\{0,1\}^n$ such that
--
--   1. every word $x\in C$ has Hamming weight exactly $w$, i.e. $\mathrm{wt}(x)=|\{i : x_i=1\}|=w$, and
--   2. any two distinct words $x\neq y$ in $C$ have Hamming distance $d_H(x,y)=|\{i : x_i\neq y_i\}|\ge d$.
--
--   The number $A(n,d,w)$ is the largest possible size of such a code. This theorem asserts the lower bound
--
--   $$
--   A(31,10,11)\ \ge\ 682 .
--   $$
--
--   That is, there are $682$ binary words of length $31$, each having exactly eleven coordinates equal to $1$, such that any two of them differ in at least ten coordinates. Equivalently, any two of the words have at most six positions of $1$ in common.
--
--   A. E. Brouwer maintains the standard table of lower bounds for $A(n,d,w)$. As of 2026-10-16 that table lists $A(31,10,11)\ge 651$, so this statement improves the best known lower bound by $31$. The code was found by a computer search, and an explicit list of its $682$ codewords is part of the proof.
--
--   **Formalization Note** A word is a function `Fin 31 → Bool`, with `true` standing for the symbol $1$. Its weight is the number of coordinates whose value is `true`, and the distance between two words is Mathlib's `hammingDist`. The code is a `Finset` of exactly $682$ such words.
-- source:
--   A. E. Brouwer, table of lower bounds for binary constant weight codes A(n,d,w), https://aeb.win.tue.nl/codes/Andw.html, entry n = 31, d = 10, w = 11: best known lower bound 651 as of 2026-10-16. The size-682 code was found by computer search and is given explicitly in the proof.

import Mathlib

theorem ConstantWeightCode.A_31_10_11_ge_682 : ∃ C : Finset (Fin 31 → Bool), C.card = 682 ∧ (∀ x ∈ C, (Finset.univ.filter (fun i => x i = true)).card = 11) ∧ (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 10 ≤ hammingDist x y) := by sorry
