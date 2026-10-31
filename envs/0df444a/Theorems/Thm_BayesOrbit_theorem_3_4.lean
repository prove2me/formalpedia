-- Prove2me | Theorems.Thm_BayesOrbit_theorem_3_4
-- name    : BayesOrbit.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:17:16.283092+00:00
-- url     : https://prove2.me/theorems/39788c42-a554-4883-9d72-d2c1ac617bdb
-- title:
--   Theorem 3.4 — Kronecker's theorem (corrected: one integer per row, all ε, integrality over the rows for every column; rectangular form)
-- statement:
--   Let $I$ and $J$ be finite sets, $\theta=(\theta_{ij})_{i\in I,j\in J}$ a real matrix and $\alpha\in\mathbb R^I$. The following are equivalent:
--
--   1. for every $\varepsilon>0$ there are integers $(u_j)_{j\in J}$ and $(v_i)_{i\in I}$ with
--   $$
--   \Bigl|\sum_{j}\theta_{ij}u_j-\alpha_i-v_i\Bigr|<\varepsilon\quad\text{for all } i\in I;
--   $$
--   2. every integer vector $(w_i)_{i\in I}$ such that $\sum_i w_i\theta_{ij}\in\mathbb Z$ for all $j\in J$ also satisfies $\sum_i w_i\alpha_i\in\mathbb Z$.
--
--   This is the inhomogeneous approximation theorem of Kronecker, in the form of Cassels (1957), Ch. 3, which the paper cites. It decides when a target in the torus $\mathbb R^I/\mathbb Z^I$ can be approached by integer combinations of the columns of $\theta$.
--
--   Differences from the source:
--   - correction: one d common to all rows, a fixed ε, and (3.10) summed over the columns for the row index l → one integer v i per row, for all ε > 0, and the integrality condition summed over the rows and required for every column; reason: the printed statement is false: for N = 2, A = 0, b = (0, 1), ε = 1/2 the second condition holds while (3.9) needs one integer d with |d| < 1/2 and |1 + d| < 1/2; the corrected form is the classical theorem of Cassels, Ch. 3, the paper cites
--   - generalization: an N × N matrix → a rectangular matrix, I indexing rows and J columns; reason: I = J is the printed shape, and the proof of Lemma 3.8 needs J of size one
-- source:
--   Hellman–Levy, Dense Orbits of the Bayesian Updating Group Action, accepted manuscript (Enlighten 227272), Theorem 3.4, eqs. (3.9), (3.10), p.15

import Mathlib

open scoped BigOperators

namespace BayesOrbit

/-- Theorem 3.4 of Hellman–Levy, Dense Orbits of the Bayesian Updating Group Action, accepted
manuscript (Enlighten 227272), p.15 (PDF 16), eqs. (3.9), (3.10), corrected: Kronecker's theorem
in the classical form the paper cites from Cassels (1957), Ch. 3.

**Formalization Note.** The statement as printed is false (`N = 2`, `A = 0`, `b = (0, 1)`,
`ε = 1/2`), so this is the corrected form: one integer `v i` per row instead of one `d`, all
`ε > 0` instead of a fixed one, and the integrality condition summed over the rows and required for
every column. The matrix is rectangular, `I` indexing rows and `J` columns; `I = J` is the printed
shape, and the proof of Lemma 3.8 needs `J` of size one. -/
theorem theorem_3_4 {I J : Type*} [Fintype I] [Fintype J] (θ : I → J → ℝ) (α : I → ℝ) :
    (∀ ε : ℝ, 0 < ε → ∃ (u : J → ℤ) (v : I → ℤ), ∀ i,
      |∑ j, θ i j * (u j : ℝ) - α i - (v i : ℝ)| < ε) ↔
    (∀ w : I → ℤ, (∀ j, ∃ z : ℤ, ∑ i, (w i : ℝ) * θ i j = (z : ℝ)) →
      ∃ z : ℤ, ∑ i, (w i : ℝ) * α i = (z : ℝ)) := by sorry

end BayesOrbit
