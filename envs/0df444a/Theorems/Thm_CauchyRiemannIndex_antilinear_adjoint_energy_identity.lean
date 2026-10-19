-- Prove2me | Theorems.Thm_CauchyRiemannIndex_antilinear_adjoint_energy_identity
-- name    : CauchyRiemannIndex.antilinear_adjoint_energy_identity
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T14:00:22.510551+00:00
-- url     : https://prove2.me/theorems/6f595bf5-2b11-4bd5-bbf6-b457b8a495dc
-- title:
--   $L^2$ identity for the adjoint Cauchy–Riemann operator with an antilinear term
-- statement:
--   Let $\beta:\mathbb R\times S^1\to\mathbb C$ be $C^1$, let $\sigma\in\mathbb R$, and for $b\in\mathbb C$ let $A(b)$ be the real $2\times2$ matrix of $z\mapsto b\bar z$ on $\mathbb C=\mathbb R^2$. For every smooth $\varphi:\mathbb R\times S^1\to\mathbb R^2$ that vanishes for large $|s|$,
--   $$\int\big|-\partial_s\varphi+J_0\partial_t\varphi+\sigma A(\beta)\varphi\big|^2=\int|\partial_s\varphi|^2+\int|\partial_t\varphi|^2+\sigma^2\!\int|\beta|^2|\varphi|^2+\sigma\!\int\big\langle\varphi,\,A(\partial_s\beta+i\,\partial_t\beta)\,\varphi\big\rangle ,$$
--   all integrals over $\mathbb R\times S^1$.
--
--   The operator on the left is the formal adjoint of $\partial_s+J_0\partial_t+\sigma\beta\bar{\cdot}$ (Wendl, § 5.5); the last term involves only $\partial_{\bar z}\beta$, so it vanishes wherever $\beta$ is holomorphic in $z=s+it$.
--
--   **Formalization Note.** $S^1=\mathbb R/\mathbb Z$; maps on the cylinder are maps of $(s,t)\in\mathbb R\times\mathbb R$ that are $1$-periodic in $t$, and integrals over $\mathbb R\times S^1$ are over the strip $\mathbb R\times[0,1)$ (`cylMeasure`). Test sections are `IsTestSection` (smooth, $1$-periodic in $t$, zero for large $|s|$); $\partial_s,\partial_t$ are `partialS`, `partialT`, and matrices act through `Matrix.toEuclideanLin`. $\mathbb C=\mathbb R^2$ via $(x,y)\mapsto x+iy$ and $A(b)$ is `antilinearMat b`; $\partial_s\beta,\partial_t\beta$ are `fderiv ℝ β x (1, 0)` and `fderiv ℝ β x (0, 1)`. The integrals are Bochner integrals over `cylMeasure`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 5, § 5.5, pp. 94–100 (n = 1)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- For a test section `φ` of the cylinder and a `C¹` function `β : ℝ × S¹ → ℂ`, with
`A(β) = antilinearMat β` the matrix of `z ↦ β z̄`,
`∫ |-∂ₛφ + J₀ ∂ₜφ + σ A(β) φ|² = ∫ |∂ₛφ|² + ∫ |∂ₜφ|² + σ² ∫ |β|² |φ|² + σ ∫ ⟨φ, A(∂ₛβ + i ∂ₜβ) φ⟩`
over `ℝ × [0, 1)`. -/
theorem antilinear_adjoint_energy_identity (β : ℝ × ℝ → ℂ) (hβ : ContDiff ℝ 1 β)
    (hβper : ∀ s t, β (s, t + 1) = β (s, t)) (σ : ℝ) (φ : ℝ × ℝ → Vec 1)
    (hφ : IsTestSection φ) :
    ∫ x, ‖-partialS φ x + Matrix.toEuclideanLin (J₀ 1) (partialT φ x) +
        Matrix.toEuclideanLin (σ • antilinearMat (β x)) (φ x)‖ ^ 2 ∂cylMeasure =
      ∫ x, ‖partialS φ x‖ ^ 2 ∂cylMeasure + ∫ x, ‖partialT φ x‖ ^ 2 ∂cylMeasure +
        σ ^ 2 * ∫ x, ‖β x‖ ^ 2 * ‖φ x‖ ^ 2 ∂cylMeasure +
        σ * ∫ x, ⟪φ x, Matrix.toEuclideanLin
          (antilinearMat (fderiv ℝ β x (1, 0) + Complex.I * fderiv ℝ β x (0, 1)))
          (φ x)⟫ ∂cylMeasure := by
  sorry

end CauchyRiemannIndex
