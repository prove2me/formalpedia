-- Prove2me | Theorems.Thm_CauchyRiemannIndex_exists_periodic_solution_bound
-- name    : CauchyRiemannIndex.exists_periodic_solution_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-14T21:00:48.083539+00:00
-- url     : https://prove2.me/theorems/e19ac9ea-0ca2-4126-b2e2-b8d50936ca92
-- title:
--   Periodic solutions of $J_0\psi'+S_\infty\psi=g$ for a nondegenerate asymptotic operator, with a uniform bound by $\|g\|_{L^1}$
-- statement:
--   Let $S_\infty:\mathbb R\to\mathbb R^{2n\times2n}$ be a continuous $1$-periodic loop of symmetric matrices whose asymptotic operator $A=-J_0\partial_t-S_\infty(t)$ is nondegenerate, where $J_0=\begin{pmatrix}0&-\mathrm{Id}\ \mathrm{Id}&0\end{pmatrix}$. Then there is a constant $C$, depending only on $S_\infty$, such that for every continuous $1$-periodic $g:\mathbb R\to\mathbb R^{2n}$ there is a continuously differentiable $1$-periodic $\psi:\mathbb R\to\mathbb R^{2n}$ with
--   $$J_0\psi'(t)+S_\infty(t)\psi(t)=g(t)\quad\text{and}\quad|\psi(t)|\le C\int_0^1|g(\tau)|\,d\tau\qquad\text{for all }t\in\mathbb R.$$
--
--   In other words, the periodic problem $-A\psi=g$ is solvable for continuous right-hand sides, with an $L^1\to L^\infty$ bound for the solution. Asymptotic operators are those of Wendl (3.10); the statement is used for the one-dimensional periodic problem underlying the translation-invariant Cauchy–Riemann operator $\partial_s+J_0\partial_t+S_\infty(t)$ on the cylinder (Wendl, Theorem 4.11).
--
--   **Formalization Note.** $\mathbb R^{2n}$ is `EuclideanSpace ℝ (Fin n ⊕ Fin n)`, $J_0$ is `Matrix.J`, and matrices act through `Matrix.toEuclideanLin`. The loop is `IsSymLoop` (continuous, $1$-periodic, symmetric values); nondegeneracy is `IsNondegenerate` ($\det(1-\Psi(1))\ne0$ for the fundamental solution $\Psi'=J_0S_\infty\Psi$, $\Psi(0)=1$). $C^1$ is `ContDiff ℝ 1`, $\psi'$ is `deriv ψ`, and $\int_0^1$ is the Bochner integral over `Set.Ico 0 1`. The constant $C$ is chosen before $g$.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3, (3.10) (asymptotic operators) and Lecture 4, Theorem 4.11, p. 71 (setting of the translation-invariant operator)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Let `S∞` be a nondegenerate loop of symmetric matrices. There is a constant `C` such that for
every continuous `1`-periodic `g : ℝ → ℝ²ⁿ` there is a `C¹` `1`-periodic `ψ : ℝ → ℝ²ⁿ` with
`J₀ ψ' + S∞ ψ = g` and `|ψ(t)| ≤ C ∫₀¹ |g|` for all `t`. -/
theorem exists_periodic_solution_bound (n : ℕ) (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf)
    (hnd : IsNondegenerate Sinf) :
    ∃ C : ℝ, ∀ g : ℝ → Vec n, Continuous g → Function.Periodic g 1 →
      ∃ ψ : ℝ → Vec n, ContDiff ℝ 1 ψ ∧ Function.Periodic ψ 1 ∧
        (∀ t, Matrix.toEuclideanLin (J₀ n) (deriv ψ t) +
          Matrix.toEuclideanLin (Sinf t) (ψ t) = g t) ∧
        ∀ t, ‖ψ t‖ ≤ C * ∫ τ in Set.Ico (0 : ℝ) 1, ‖g τ‖ := by
  sorry

end CauchyRiemannIndex
