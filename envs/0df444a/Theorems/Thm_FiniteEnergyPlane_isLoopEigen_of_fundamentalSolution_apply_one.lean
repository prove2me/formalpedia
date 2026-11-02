-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isLoopEigen_of_fundamentalSolution_apply_one
-- name    : FiniteEnergyPlane.isLoopEigen_of_fundamentalSolution_apply_one
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T22:36:27.183001+00:00
-- url     : https://prove2.me/theorems/b37899b4-0402-4aa6-b764-915913814e63
-- title:
--   A fixed vector of the monodromy of the asymptotic operator gives an eigenfunction
-- statement:
--   Let $S_\infty:\mathbb{R}\to\mathbb{R}^{2n\times2n}$ be a $C^\infty$ $1$-periodic loop of symmetric matrices, $\mu\in\mathbb{R}$, and let $\Psi:\mathbb{R}\to\mathbb{R}^{2n\times2n}$ be the fundamental solution of $S_\infty+\mu$, i.e. $\Psi(0)=\mathrm{Id}$ and $\Psi'(t)=J_0(S_\infty(t)+\mu)\Psi(t)$. If $v\neq0$ satisfies $\Psi(1)v=v$, then $e(t)=\Psi(t)v$ is an eigenfunction of $A=-J_0\partial_t-S_\infty$ with eigenvalue $\mu$: $e$ is $C^\infty$, $1$-periodic, not identically zero, and $-J_0e'-S_\infty e=\mu e$.
--
--   The converse direction of the correspondence between eigenfunctions of the asymptotic operator and fixed vectors of the time-one monodromy of the shifted equation; it turns fixed vectors of $\Psi(1)$ into eigenfunctions.
--
--   **Formalization Note** The fundamental solution is `CauchyRiemannIndex.IsFundamentalSolution (fun t => Sinf t + μ • 1) Ψ`; $\Psi(t)v$ is `Matrix.toEuclideanLin (Ψ t) v`; eigenfunctions are `IsLoopEigen Sinf μ` (`FiniteEnergyPlane_Asymptotics`).
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory (2026 notes), arXiv:1612.01009, Section 3.7; H. Hofer, K. Wysocki, E. Zehnder, GAFA 5 (1995), Section 3.

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_existsUnique

namespace FiniteEnergyPlane

open scoped ContDiff

/-- Let `Ψ` be the fundamental solution of `S∞ + μ`. If `v ≠ 0` is fixed by `Ψ(1)`, then
`t ↦ Ψ(t) v` is an eigenfunction of `A = -J₀ ∂ₜ - S∞` with eigenvalue `μ`. -/
theorem isLoopEigen_of_fundamentalSolution_apply_one {n : ℕ}
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) (μ : ℝ)
    (Ψ : ℝ → CauchyRiemannIndex.Mat n)
    (hΨ : CauchyRiemannIndex.IsFundamentalSolution
      (fun t => Sinf t + μ • (1 : CauchyRiemannIndex.Mat n)) Ψ)
    (v : CauchyRiemannIndex.Vec n) (hv : v ≠ 0) (h1 : Matrix.toEuclideanLin (Ψ 1) v = v) :
    IsLoopEigen Sinf μ (fun t => Matrix.toEuclideanLin (Ψ t) v) := by
  sorry

end FiniteEnergyPlane
