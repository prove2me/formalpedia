-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_isLoopEigen_hasLoopEigenWind_of_extremal_angle
-- name    : FiniteEnergyPlane.exists_isLoopEigen_hasLoopEigenWind_of_extremal_angle
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T23:05:26.411286+00:00
-- url     : https://prove2.me/theorems/c15c2bc9-0c7a-425a-934d-030c432944af
-- title:
--   An extremal angle displacement of the fundamental solution equal to 2πk gives an eigenvalue of winding k
-- statement:
--   Let $S_\infty:\mathbb{R}\to\mathbb{R}^{2\times2}$ be a $C^\infty$ $1$-periodic loop of symmetric matrices, $A=-J_0\partial_t-S_\infty$, $\mu\in\mathbb{R}$, and $\Psi$ the fundamental solution of $S_\infty+\mu$. Identify $\mathbb{R}^2$ with $\mathbb{C}$. Suppose $\Psi(t)v\neq0$ for $v\neq0$, and let $\theta(\alpha,t)$ be functions, continuous in $t$, with $\theta(\alpha,0)=\alpha$, $\Psi(t)e^{i\alpha}=|\Psi(t)e^{i\alpha}|\,e^{i\theta(\alpha,t)}$ for all $\alpha,t$, and $\alpha\mapsto\theta(\alpha,1)$ continuous. Let $k\in\mathbb{Z}$ and $\alpha_0\in\mathbb{R}$ with $\theta(\alpha_0,1)-\alpha_0=2\pi k$, and suppose that $2\pi k$ is the maximum, or the minimum, of $\beta\mapsto\theta(\beta,1)-\beta$ over $\mathbb{R}$. Then $\mu$ is an eigenvalue of $A$ all of whose eigenfunctions have winding number $k$, and it has an eigenfunction $e$ with $e(0)=e^{i\alpha_0}$.
--
--   The function $\theta(\beta,1)-\beta$ is the angle swept in one period by the solution of $-J_0x'-S_\infty x=\mu x$ starting at $e^{i\beta}$. The statement identifies eigenvalues of a given winding number from extremal values of this displacement.
--
--   **Formalization Note** Eigenfunctions are `IsLoopEigen Sinf μ`, and "every eigenfunction of $\mu$ has winding $k$" is `HasLoopEigenWind Sinf μ k`; the identification with $\mathbb{C}$ is `vecToC`; the max/min hypothesis is `(∀ β, θ β 1 - β ≤ 2 * π * k) ∨ (∀ β, 2 * π * k ≤ θ β 1 - β)`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory (2026 notes), arXiv:1612.01009, Section 3.7, proof of Theorem 3.7.1; H. Hofer, K. Wysocki, E. Zehnder, GAFA 5 (1995), Section 3.

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open Filter Topology
open scoped Real ContDiff

/-- Let `Ψ` be the fundamental solution of `S∞ + μ` and `θ α t` continuous arguments of
`Ψ(t) e^{iα}` with `θ α 0 = α`, continuous in `α` at `t = 1`. If the angle displacement
`θ α₀ 1 - α₀` equals `2πk` and `2πk` is the maximum or the minimum of `β ↦ θ β 1 - β`, then
`μ` is an eigenvalue of winding `k`, with an eigenfunction `e` satisfying `e 0 = e^{iα₀}`. -/
theorem exists_isLoopEigen_hasLoopEigenWind_of_extremal_angle (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) (μ : ℝ)
    (Ψ : ℝ → CauchyRiemannIndex.Mat 1)
    (hΨ : CauchyRiemannIndex.IsFundamentalSolution
      (fun t => Sinf t + μ • (1 : CauchyRiemannIndex.Mat 1)) Ψ)
    (θ : ℝ → ℝ → ℝ)
    (hne : ∀ (t : ℝ) (v : CauchyRiemannIndex.Vec 1), v ≠ 0 → Matrix.toEuclideanLin (Ψ t) v ≠ 0)
    (hθc : ∀ α, Continuous (θ α)) (hθ0 : ∀ α, θ α 0 = α)
    (hrep : ∀ (α : ℝ) (v : CauchyRiemannIndex.Vec 1), vecToC v = Complex.exp (α * Complex.I) →
      ∀ t, vecToC (Matrix.toEuclideanLin (Ψ t) v) =
        (‖vecToC (Matrix.toEuclideanLin (Ψ t) v)‖ : ℂ) * Complex.exp (θ α t * Complex.I))
    (hD : Continuous fun α => θ α 1) (k : ℤ) (α₀ : ℝ) (hα : θ α₀ 1 - α₀ = 2 * π * k)
    (hext : (∀ β, θ β 1 - β ≤ 2 * π * k) ∨ (∀ β, 2 * π * k ≤ θ β 1 - β)) :
    ∃ e, IsLoopEigen Sinf μ e ∧ HasLoopEigenWind Sinf μ k ∧
      vecToC (e 0) = Complex.exp (α₀ * Complex.I) := by
  sorry

end FiniteEnergyPlane
