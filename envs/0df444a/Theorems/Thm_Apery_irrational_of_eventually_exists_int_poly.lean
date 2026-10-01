-- Prove2me | Theorems.Thm_Apery_irrational_of_eventually_exists_int_poly
-- name    : Apery.irrational_of_eventually_exists_int_poly
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-01T10:41:28.728071+00:00
-- url     : https://prove2.me/theorems/fdc353f4-de22-4613-b159-3f01ffd08476
-- title:
--   Irrationality from small values of integer polynomials
-- statement:
--   Let $\xi\in\mathbb R$, $d:\mathbb N\to\mathbb N$, and $\varepsilon:\mathbb N\to\mathbb R$. Assume that for every positive integer $b$,
--   $$b^{d(n)}\varepsilon_n\longrightarrow0.$$
--   Suppose every sufficiently large $n$ admits $Q\in\mathbb Z[X]$ such that
--   $$\deg Q\le d(n),\qquad 0<Q(\xi)\le\varepsilon_n.$$
--   Then $\xi$ is irrational. No coefficient-height bound or monotonicity hypothesis is imposed. The positive evaluation excludes the zero polynomial. This is the general criterion consumed by the project's final irrationality argument.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Criterion.lean#L40-L72

import Mathlib

open Polynomial Filter Topology MeasureTheory

namespace Apery

theorem irrational_of_eventually_exists_int_poly (ξ : ℝ) (d : ℕ → ℕ) (ε : ℕ → ℝ)
    (hε : ∀ b : ℕ, 0 < b → Tendsto (fun n => (b : ℝ) ^ d n * ε n) atTop (𝓝 0))
    (h : ∀ᶠ n in atTop, ∃ Q : ℤ[X], Q.natDegree ≤ d n ∧ 0 < aeval ξ Q ∧ aeval ξ Q ≤ ε n) :
    Irrational ξ := by sorry

end Apery
