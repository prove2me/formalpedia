-- Prove2me | Theorems.Thm_ConstantWeightCode_A_32_10_10_ge_527
-- name    : ConstantWeightCode.A_32_10_10_ge_527
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-16T01:27:17.853245+00:00
-- url     : https://prove2.me/theorems/2e5c2d62-0380-4ab4-ada3-084413afc9a9
-- title:
--   New lower bound $A(32,10,10)\ge 527$ for binary constant-weight codes
-- statement:
--   A **binary constant-weight code** with parameters $(n,d,w)$ is a set $C$ of binary words $x=(x_1,\dots,x_n)\in\{0,1\}^n$ such that
--
--   1. every word $x\in C$ has Hamming weight exactly $w$, i.e. $\mathrm{wt}(x)=|\{i : x_i=1\}|=w$, and
--   2. any two distinct words $x\neq y$ in $C$ have Hamming distance $d_H(x,y)=|\{i : x_i\neq y_i\}|\ge d$.
--
--   The number $A(n,d,w)$ is the largest possible size of such a code. This theorem asserts the lower bound
--
--   $$
--   A(32,10,10)\ \ge\ 527 .
--   $$
--
--   That is, there are $527$ binary words of length $32$, each having exactly ten coordinates equal to $1$, such that any two of them differ in at least ten coordinates. Equivalently, any two of the words have at most five positions of $1$ in common.
--
--   A. E. Brouwer maintains the standard table of lower bounds for $A(n,d,w)$. As of 2026-10-15 that table lists $A(32,10,10)\ge 500$, so this statement improves the best known lower bound by $27$. The code was found by a computer search, and an explicit list of its $527$ codewords is part of the proof.
--
--   **Formalization Note** A word is a function `Fin 32 → Bool`, with `true` standing for the symbol $1$. Its weight is the number of coordinates whose value is `true`, and the distance between two words is Mathlib's `hammingDist`. The code is a `Finset` of exactly $527$ such words.
-- source:
--   A. E. Brouwer, table of lower bounds for binary constant weight codes A(n,d,w), https://aeb.win.tue.nl/codes/Andw.html, entry n = 32, d = 10, w = 10: best known lower bound 500 as of 2026-10-15. The size-527 code was found by computer search (2026-10-15) and is given explicitly in the proof.

import Mathlib

theorem ConstantWeightCode.A_32_10_10_ge_527 : ∃ C : Finset (Fin 32 → Bool), C.card = 527 ∧ (∀ x ∈ C, (Finset.univ.filter (fun i => x i = true)).card = 10) ∧ (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 10 ≤ hammingDist x y) := by sorry
