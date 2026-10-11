-- Prove2me | Theorems.Thm_AsymptoticOperator_linearODE_existsUnique
-- name    : AsymptoticOperator.linearODE_existsUnique
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T23:18:08.667877+00:00
-- url     : https://prove2.me/theorems/65ed9439-455d-479e-a41c-c318e7576776
-- title:
--   Global existence and uniqueness for linear ODEs with continuous operator coefficients
-- statement:
--   Let $E$ be a real Banach space and let $B:\mathbb{R}\to\mathcal{L}(E)$ be continuous with respect to the operator norm. For every $x_0\in E$ there is exactly one function $x:\mathbb{R}\to E$ with $x(0)=x_0$ that is differentiable at every $t\in\mathbb{R}$ with $x'(t)=B(t)\,x(t)$.
--
--   This is global existence and uniqueness for linear non-autonomous equations on the whole real line, with no boundedness assumption on $B$. Taking $E$ to be the space of real $2n\times 2n$ matrices and $B(t)X=J_0S(t)X$, it provides the fundamental solution $\Psi'=J_0S\Psi$, $\Psi(0)=\mathrm{Id}$, of a loop of matrices $S$.
--
--   **Formalization Note.** $E$ is a `NormedAddCommGroup` with `NormedSpace ℝ E` and `CompleteSpace E`; `B : ℝ → E →L[ℝ] E` with `Continuous B` (operator-norm topology). The conclusion is `∃! x : ℝ → E, x 0 = x₀ ∧ ∀ t, HasDerivAt x (B t (x t)) t`, so uniqueness holds among all functions $\mathbb{R}\to E$ with these properties.
-- source:
--   Auxiliary statement for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 3, §3.2 (fundamental solution of an asymptotic operator)

import Mathlib.Analysis.ODE.ExistUnique

namespace AsymptoticOperator

/-- For a continuous family `B : ℝ → (E →L[ℝ] E)` of bounded operators on a real Banach space
and any initial value `x₀`, the linear equation `x' = B(t) x` has exactly one solution
`x : ℝ → E` defined on all of `ℝ` with `x 0 = x₀`. -/
theorem linearODE_existsUnique {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (B : ℝ → E →L[ℝ] E) (hB : Continuous B) (x₀ : E) :
    ∃! x : ℝ → E, x 0 = x₀ ∧ ∀ t, HasDerivAt x (B t (x t)) t := by sorry

end AsymptoticOperator
