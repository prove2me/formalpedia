-- Prove2me | Theorems.Thm_FiniteEnergyPlane_eigenEq_fundamentalSolution_apply
-- name    : FiniteEnergyPlane.eigenEq_fundamentalSolution_apply
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T23:01:30.818998+00:00
-- url     : https://prove2.me/theorems/1312494d-0a0e-41a9-9dde-e451744fe332
-- title:
--   Columns of the fundamental solution of the shifted equation solve the eigenvalue equation of the asymptotic operator
-- statement:
--   Let $S_\infty:\mathbb{R}\to\mathbb{R}^{2\times2}$ be a loop of real matrices, $\mu\in\mathbb{R}$, and let $\Psi$ be the fundamental solution of $S_\infty+\mu$: $\Psi(0)=\mathrm{Id}$ and $\Psi'(t)=J_0(S_\infty(t)+\mu)\Psi(t)$ for all $t$. Then for every $w\in\mathbb{R}^2$ the path $x(t)=\Psi(t)w$ is differentiable on $\mathbb{R}$ and satisfies $-J_0x'(t)-S_\infty(t)x(t)=\mu\,x(t)$ for all $t$.
--
--   The solutions of the eigenvalue equation of $A=-J_0\partial_t-S_\infty$ on the line (not necessarily periodic) are exactly $t\mapsto\Psi(t)w$; this records the easy inclusion in the form used with the cross-term identities for such solutions.
--
--   **Formalization Note** $\Psi(t)w$ is `Matrix.toEuclideanLin (Ψ t) w`; the fundamental solution is `CauchyRiemannIndex.IsFundamentalSolution (fun t => Sinf t + μ • 1) Ψ`; the equation is stated with `deriv`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory (2026 notes), arXiv:1612.01009, Section 3.7, proof of Theorem 3.7.1; H. Hofer, K. Wysocki, E. Zehnder, GAFA 5 (1995), Section 3.

import Definitions.Def_FiniteEnergyPlane_Winding
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace FiniteEnergyPlane

open Filter Topology
open scoped Real ContDiff

/-- If `Ψ` is the fundamental solution of `S∞ + μ` (`n = 1`), then for every `w` the path
`t ↦ Ψ(t) w` is differentiable and solves `-J₀ x' - S∞ x = μ x` on `ℝ`. -/
theorem eigenEq_fundamentalSolution_apply (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (μ : ℝ)
    (Ψ : ℝ → CauchyRiemannIndex.Mat 1)
    (hΨ : CauchyRiemannIndex.IsFundamentalSolution
      (fun t => Sinf t + μ • (1 : CauchyRiemannIndex.Mat 1)) Ψ)
    (w : CauchyRiemannIndex.Vec 1) :
    Differentiable ℝ (fun t => Matrix.toEuclideanLin (Ψ t) w) ∧
      ∀ t, -(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1)
        (deriv (fun t => Matrix.toEuclideanLin (Ψ t) w) t)) -
          Matrix.toEuclideanLin (Sinf t) (Matrix.toEuclideanLin (Ψ t) w) =
        μ • Matrix.toEuclideanLin (Ψ t) w := by
  sorry

end FiniteEnergyPlane
