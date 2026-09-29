-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_exists_isAffineOpen_smooth_rank_eq_etaleCoordinates_of_point
-- name    : AlgebraicGeometry.SmoothOfRelativeDimension.exists_isAffineOpen_smooth_rank_eq_etaleCoordinates_of_point
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/78627342-b3a4-51b4-80cb-d96170885b28
-- title:
--   Affine chart with étale coordinates at a rational point
-- statement:
--   Let $k$ be a field, $M$ a scheme, $\pi_M : M \to \operatorname{Spec} k$ a morphism satisfying `SmoothOfRelativeDimension n πM` for a natural number $n$, and let $\sigma : \operatorname{Spec} k \to M$ be a section of $\pi_M$, i.e. $\sigma$ followed by $\pi_M$ is the identity. The assertion is that there exist an open subscheme $U \subseteq M$, a proof that $U$ is affine, and an inclusion $\top \le \sigma^{-1}U$ (so the whole of $\operatorname{Spec} k$ maps into $U$ under $\sigma$) such that, when $S := \Gamma(M,U)$ is made a $k$-algebra by the structure map $\pi_M$ induces on sections over $U$ (the composite of the inverse of $\Gamma\mathrm{Spec}$-iso with $\pi_M^\sharp : \Gamma(\operatorname{Spec} k, \top) \to \Gamma(M,U)$), the following hold: $S$ is an integral domain; $S$ is of finite type over $k$; $S$ is smooth over $k$ in the sense of `Algebra.Smooth`; the module rank of $\Omega_{S/k}$ over $S$ equals $n$; and there are a $k$-algebra homomorphism $\sigma_0 : S \to k$ and elements $t_i \in S$, $i \in \mathrm{Fin}\,n$, such that $\sigma_0$ is evaluation at $\sigma$, namely $\sigma_0(s)$ is the image of $\sigma^\sharp(s)$ under the $\Gamma\mathrm{Spec}$-isomorphism for every $s \in S$, such that $\sigma_0(t_i) = 0$ for all $i$, and such that $(\ker \sigma_0)\,\Omega_{S/k} + \sum_i S\,\mathrm{d}t_i = \Omega_{S/k}$.
--
--   This is the existence of an affine neighbourhood of a $k$-rational point on a scheme smooth of relative dimension $n$ over $k$ on which the coordinate ring is a smooth finite-type domain with free differentials of rank $n$, together with a system of étale coordinates $t_1,\dots,t_n$ vanishing at the point. It supplies exactly the algebraic input for the construction of analytic charts near the identity in [`GoodReductionJacobian.RelativeGroupLaw.exists_chart_differentiableOn_mul_of_smoothOfRelativeDimension`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_chart_differentiableOn_mul_of_smoothOfRelativeDimension), where $k = \mathbb{C}$ and the $t_i$ become local holomorphic coordinates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothOfRelativeDimension_exists_isAffineOpen_smooth_rank_eq_etaleCoordinates_of_point.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_KaehlerModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite

theorem AlgebraicGeometry.SmoothOfRelativeDimension.exists_isAffineOpen_smooth_rank_eq_etaleCoordinates_of_point
    {k : Type} [Field k] (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of k)) {n : ℕ}
    (hsm : SmoothOfRelativeDimension n πM)
    (σ : Spec (CommRingCat.of k) ⟶ M) (hσ : σ ≫ πM = 𝟙 _) :
    ∃ (U : M.Opens) (hU : IsAffineOpen U) (hσU : ⊤ ≤ σ ⁻¹ᵁ U),
      letI := πM.sectionsAlgebra U
      IsDomain Γ(M, U) ∧ Algebra.FiniteType k Γ(M, U) ∧ Algebra.Smooth k Γ(M, U) ∧
      Module.rank Γ(M, U) (KaehlerDifferential k Γ(M, U)) = n ∧
      ∃ (σ₀ : Γ(M, U) →ₐ[k] k) (t : Fin n → Γ(M, U)),
        (∀ s : Γ(M, U), σ₀ s = (Scheme.ΓSpecIso (CommRingCat.of k)).hom ((σ.appLE U ⊤ hσU) s)) ∧
        (∀ i : Fin n, σ₀ (t i) = 0) ∧
        (RingHom.ker σ₀.toRingHom) • (⊤ : Submodule Γ(M, U) (KaehlerDifferential k Γ(M, U))) ⊔
          Submodule.span Γ(M, U) (Set.range fun i : Fin n => KaehlerDifferential.D k Γ(M, U) (t i)) = ⊤ := by sorry
