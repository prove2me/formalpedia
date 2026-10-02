-- Prove2me | Theorems.Thm_AppliedComb_Recurrence_nonhomogeneous
-- name    : AppliedComb.Recurrence.nonhomogeneous
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:15:19.239215+00:00
-- url     : https://prove2.me/theorems/f7fddcbd-5d6d-4dc9-aa12-2bf1425370c3
-- title:
--   Lemma 9.20 — every solution of p(A)f = g is a particular solution plus a homogeneous one
-- statement:
--   Let $V$ be the space of functions $f : \mathbb{Z} \to \mathbb{R}$, $A$ the advancement operator, $k \ge 0$ an integer and $c_0, \dots, c_k$ real constants with $c_0 \neq 0$ and $c_k \neq 0$. Let $g \in V$ be arbitrary and consider the nonhomogeneous equation
--
--   $$p(A) f = (c_0 A^k + c_1 A^{k-1} + c_2 A^{k-2} + \cdots + c_k) f = g, \qquad (9.5.2)$$
--
--   and let $W$ be the subspace of $V$ of all solutions of the homogeneous equation $p(A) f = 0$ (9.5.3). If $f_0$ is a solution of (9.5.2), then every solution $f$ of (9.5.2) can be written as $f = f_0 + f_1$ with $f_1 \in W$.
--
--   Together with a description of $W$ this reduces the nonhomogeneous equation to finding one particular solution; it is used in the inductive step of Theorem 9.21.
--
--   **Formalization Note.** $p(A)$ is `opPoly k c` and $W$ is `solutionSpace k c` (the kernel of `opPoly k c`). The hypotheses $c_0 \neq 0$ and $c_k \neq 0$ are kept because the book states them, although the conclusion does not need them.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 200, Lemma 9.20

import Mathlib
import Definitions.Def_AppliedComb_Recurrence_advance

namespace AppliedComb.Recurrence

/-- Keller–Trotter, Lemma 9.20 (p. 200). Consider the nonhomogeneous equation
`p(A) f = (c₀ A^k + c₁ A^(k-1) + ⋯ + c_k) f = g` (9.5.2) with `c₀, c_k ≠ 0` and an arbitrary
right-hand side `g : ℤ → ℝ`, and let `W` be the solution space of the homogeneous equation
`p(A) f = 0` (9.5.3). If `f₀` is a solution to (9.5.2), then every solution `f` to (9.5.2) has
the form `f = f₀ + f₁` with `f₁ ∈ W`. -/
theorem nonhomogeneous (k : ℕ) (c : Fin (k + 1) → ℝ) (hc0 : c 0 ≠ 0)
    (hck : c (Fin.last k) ≠ 0) (g f₀ : ℤ → ℝ) (hf₀ : opPoly k c f₀ = g) :
    ∀ f : ℤ → ℝ, opPoly k c f = g → ∃ f₁ ∈ solutionSpace k c, f = f₀ + f₁ := by sorry

end AppliedComb.Recurrence
