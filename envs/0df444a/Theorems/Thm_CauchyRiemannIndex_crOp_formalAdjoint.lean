-- Prove2me | Theorems.Thm_CauchyRiemannIndex_crOp_formalAdjoint
-- name    : CauchyRiemannIndex.crOp_formalAdjoint
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-13T22:33:09.468977+00:00
-- url     : https://prove2.me/theorems/1d97002a-21bc-4a7a-8749-720090da14c0
-- title:
--   Formal adjoint of a Cauchy–Riemann operator on the cylinder
-- statement:
--   Let $S:\mathbb R\times\mathbb R\to\mathbb R^{2n\times2n}$ be continuous. For all smooth $u,v:\mathbb R\times S^1\to\mathbb R^{2n}$ that vanish for large $|s|$,
--   $$\int_{\mathbb R\times S^1}\big\langle \partial_su+J_0\partial_tu+S\,u,\ v\big\rangle=\int_{\mathbb R\times S^1}\big\langle u,\ -\partial_sv+J_0\partial_tv+S^{T}v\big\rangle .$$
--   So the formal $L^2$-adjoint of $D_S=\partial_s+J_0\partial_t+S$ is $-\partial_s+J_0\partial_t+S^T$.
--
--   This identity is used for duality arguments with Cauchy–Riemann operators on the cylinder (Wendl, Lecture 4).
--
--   **Formalization Note.** $S^1=\mathbb R/\mathbb Z$; maps on the cylinder are maps of $(s,t)\in\mathbb R\times\mathbb R$ that are $1$-periodic in $t$, and $L^p(\mathbb R\times S^1)$ is $L^p$ of the strip $\mathbb R\times[0,1)$ (`cylMeasure`). Test sections are `IsTestSection` (smooth, $1$-periodic in $t$, zero for large $|s|$). The integrals are Bochner integrals over `cylMeasure` of `inner ℝ` on `EuclideanSpace ℝ (Fin n ⊕ Fin n)`; $D_Su$ is `crOp S u`, $\partial_s,\partial_t$ are `partialS`, `partialT`, and $J_0$, $S^T$ act through `Matrix.toEuclideanLin`. $S$ is not assumed periodic.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, Theorem 4.11, p. 71 (case k = 1)

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- The formal adjoint of `D_S = ∂ₛ + J₀ ∂ₜ + S(s, t)` on the cylinder `ℝ × S¹` is
`-∂ₛ + J₀ ∂ₜ + S(s, t)ᵀ`: for a continuous `S` and test sections `u`, `v`,
`∫ ⟨D_S u, v⟩ = ∫ ⟨u, -∂ₛv + J₀ ∂ₜv + Sᵀ v⟩` over `ℝ × [0, 1)`. -/
theorem crOp_formalAdjoint (n : ℕ) (S : ℝ × ℝ → Mat n) (hS : Continuous S)
    (u v : ℝ × ℝ → Vec n) (hu : IsTestSection u) (hv : IsTestSection v) :
    ∫ x, inner ℝ (crOp S u x) (v x) ∂cylMeasure =
      ∫ x, inner ℝ (u x) (-partialS v x + Matrix.toEuclideanLin (J₀ n) (partialT v x) +
        Matrix.toEuclideanLin (S x)ᵀ (v x)) ∂cylMeasure := by
  sorry

end CauchyRiemannIndex
