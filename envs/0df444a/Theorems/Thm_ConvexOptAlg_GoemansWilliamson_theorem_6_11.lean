-- Prove2me | Theorems.Thm_ConvexOptAlg_GoemansWilliamson_theorem_6_11
-- name    : ConvexOptAlg.GoemansWilliamson.theorem_6_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T19:23:07.029905+00:00
-- url     : https://prove2.me/theorems/290d356e-6642-468a-acc0-cc9d9abae3b8
-- title:
--   Theorem 6.11, p. 345 — Goemans–Williamson: E ζ⊤Lζ ≥ 0.878 max over {−1,1}ⁿ of x⊤Lx for ζ = sign(ξ), ξ ∼ N(0, Σ)
-- statement:
--   Let $A\in\mathbb R^{n\times n}_+$ be a symmetric matrix of non-negative weights and $L=D-A$ its graph Laplacian, $D$ being diagonal with entries $\sum_j A_{i,j}$. Let $\Sigma$ be a solution of the SDP relaxation of MAXCUT,
--
--   $$\Sigma\in\arg\max\bigl\{\langle L,X\rangle : X\in\mathbb S^n_+,\ X_{i,i}=1,\ i\in[n]\bigr\}.$$
--
--   Let $\xi\sim\mathcal N(0,\Sigma)$ and $\zeta=\operatorname{sign}(\xi)\in\{-1,1\}^n$. Then $\zeta^\top L\zeta$ is integrable and
--
--   $$\mathbb E\,\zeta^\top L\zeta\ \ge\ 0.878\max_{x\in\{-1,1\}^n}x^\top Lx.$$
--
--   This is the Goemans–Williamson guarantee: rounding the solution of a semidefinite program by a random Gaussian hyperplane produces, in expectation, a cut within a factor $0.878$ of the maximum cut, whereas a uniformly random cut only guarantees the factor $1/2$.
--
--   **Formalization Note** "The solution" is any maximizer of the relaxation (`IsSDPRelaxationOptimum`); maximizers exist because the feasible set is nonempty and compact. $\mathcal N(0,\Sigma)$ is Mathlib's `multivariateGaussian 0 Σ`, defined also for singular $\Sigma$ (e.g. $\Sigma=xx^\top$). The sign is $\{-1,1\}$-valued with $\operatorname{sign}(0)=1$. The maximum over the hypercube is a finite maximum over the $2^n$ sign vectors. Integrability of the bounded integrand is part of the conclusion. The constant $0.878$ is the book's.
-- source:
--   Bubeck, arXiv:1405.4980v2, Theorem 6.11, p. 345; MAXCUT and L = D − A, p. 344

import Mathlib
import Definitions.Def_ConvexOptAlg_GoemansWilliamson_Defs

namespace ConvexOptAlg.GoemansWilliamson

open MeasureTheory ProbabilityTheory Matrix

/-- **Theorem 6.11** (Goemans–Williamson; Bubeck, arXiv:1405.4980v2, §6.6, p. 345). Let
`A ∈ ℝ₊ⁿˣⁿ` be a symmetric matrix of non-negative weights and `L = D − A` its graph Laplacian.
Let `Σ` be the solution to the SDP relaxation of MAXCUT. Let `ξ ∼ N(0, Σ)` and
`ζ = sign(ξ) ∈ {−1, 1}ⁿ`. Then `E ζ⊤Lζ ≥ 0.878 max_{x ∈ {−1,1}ⁿ} x⊤Lx`.

`Σ` is any maximizer of `⟨L, X⟩` over `X ∈ S₊ⁿ` with unit diagonal; `N(0, Σ)` is Mathlib's
`multivariateGaussian 0 Σ` (well defined for singular `Σ`). The integrand is bounded and
measurable; its integrability is asserted as part of the conclusion. -/
theorem theorem_6_11 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hsymm : A.IsSymm)
    (hnonneg : ∀ i j, 0 ≤ A i j) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hopt : IsSDPRelaxationOptimum (laplacian A) Sig) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin n) => sgnVec ξ ⬝ᵥ laplacian A *ᵥ sgnVec ξ)
        (multivariateGaussian 0 Sig) ∧
      ∫ ξ, sgnVec ξ ⬝ᵥ laplacian A *ᵥ sgnVec ξ ∂(multivariateGaussian 0 Sig) ≥
        (0.878 : ℝ) * hypercubeMax (laplacian A) := by sorry

end ConvexOptAlg.GoemansWilliamson
