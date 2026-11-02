-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_angle_fundamentalSolution
-- name    : FiniteEnergyPlane.exists_angle_fundamentalSolution
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T22:51:25.723928+00:00
-- url     : https://prove2.me/theorems/5c54a6a8-ce90-476d-b5ca-dbb3ed6b1983
-- title:
--   Continuous angle functions for the fundamental solution of the shifted asymptotic equation in the plane
-- statement:
--   Let $S_\infty:\mathbb{R}\to\mathbb{R}^{2\times2}$ be a continuous $1$-periodic loop of symmetric matrices and, for each $\mu\in\mathbb{R}$, let $\Psi_\mu$ be the fundamental solution of $S_\infty+\mu$: $\Psi_\mu(0)=\mathrm{Id}$, $\Psi_\mu'(t)=J_0(S_\infty(t)+\mu)\Psi_\mu(t)$. Identify $\mathbb{R}^2$ with $\mathbb{C}$ by $(q,p)\mapsto q+ip$. Then there are a constant $C$ and a function $\theta(\mu,\alpha,t)$ such that:
--   1. $\Psi_\mu(t)v\neq0$ for all $v\neq0$;
--   2. for all $\mu,\alpha$, $t\mapsto\theta(\mu,\alpha,t)$ is continuous, $\theta(\mu,\alpha,0)=\alpha$ and $\theta(\mu,\alpha+2\pi,t)=\theta(\mu,\alpha,t)+2\pi$;
--   3. if $v=e^{i\alpha}$, then $\Psi_\mu(t)v=|\Psi_\mu(t)v|\,e^{i\theta(\mu,\alpha,t)}$ for all $t$;
--   4. $(\mu,\alpha)\mapsto\theta(\mu,\alpha,1)$ is continuous on $\mathbb{R}^2$;
--   5. $|\theta(\mu,\alpha,1)-\alpha-\mu|\le C$ for all $\mu,\alpha$.
--
--   So $\theta(\mu,\alpha,1)-\alpha$ is the total angle swept by the solution of $-J_0x'-S_\infty x=\mu x$ starting at $e^{i\alpha}$ over one period; it depends continuously on $(\mu,\alpha)$ and stays within a bounded distance of $\mu$. These angles are the basic data for locating the eigenvalues of $A=-J_0\partial_t-S_\infty$ with a given winding number.
--
--   **Formalization Note** $\Psi_\mu(t)v$ is `Matrix.toEuclideanLin (Ψ μ t) v`, the identification with $\mathbb{C}$ is `vecToC` (`FiniteEnergyPlane_Winding`), and the fundamental solution is `CauchyRiemannIndex.IsFundamentalSolution`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory (2026 notes), arXiv:1612.01009, Section 3.7, proof of Theorem 3.7.1; H. Hofer, K. Wysocki, E. Zehnder, GAFA 5 (1995), Section 3.

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open scoped Real

/-- Let `Ψ μ` be the fundamental solution of `S∞ + μ` (`n = 1`). There are a constant `C` and
angles `θ μ α t` such that: `Ψ μ t` is injective; `θ μ α` is continuous with `θ μ α 0 = α` and
`θ μ (α + 2π) = θ μ α + 2π`; for `v = e^{iα}` (in `ℂ` via `vecToC`), `θ μ α t` is an argument of
`Ψ μ t v`; the endpoint angle `(μ, α) ↦ θ μ α 1` is continuous; and
`|θ μ α 1 - α - μ| ≤ C`. -/
theorem exists_angle_fundamentalSolution (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hSinf : CauchyRiemannIndex.IsSymLoop Sinf) (Ψ : ℝ → ℝ → CauchyRiemannIndex.Mat 1)
    (hΨ : ∀ μ, CauchyRiemannIndex.IsFundamentalSolution
      (fun t => Sinf t + μ • (1 : CauchyRiemannIndex.Mat 1)) (Ψ μ)) :
    ∃ (C : ℝ) (θ : ℝ → ℝ → ℝ → ℝ),
      (∀ (μ t : ℝ) (v : CauchyRiemannIndex.Vec 1), v ≠ 0 → Matrix.toEuclideanLin (Ψ μ t) v ≠ 0) ∧
      (∀ μ α, Continuous (θ μ α)) ∧ (∀ μ α, θ μ α 0 = α) ∧
      (∀ μ α t, θ μ (α + 2 * π) t = θ μ α t + 2 * π) ∧
      (∀ (μ α : ℝ) (v : CauchyRiemannIndex.Vec 1), vecToC v = Complex.exp (α * Complex.I) → ∀ t,
        vecToC (Matrix.toEuclideanLin (Ψ μ t) v) =
          (‖vecToC (Matrix.toEuclideanLin (Ψ μ t) v)‖ : ℂ) *
            Complex.exp (θ μ α t * Complex.I)) ∧
      Continuous (fun p : ℝ × ℝ => θ p.1 p.2 1) ∧
      ∀ μ α, |θ μ α 1 - α - μ| ≤ C := by
  sorry

end FiniteEnergyPlane
