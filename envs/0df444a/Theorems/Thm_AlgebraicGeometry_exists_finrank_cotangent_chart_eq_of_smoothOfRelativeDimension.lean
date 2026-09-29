-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_finrank_cotangent_chart_eq_of_smoothOfRelativeDimension
-- name    : AlgebraicGeometry.exists_finrank_cotangent_chart_eq_of_smoothOfRelativeDimension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/6b4a2ad5-3b9d-5818-a5ad-7f70f520535c
-- title:
--   Cotangent space at a rational point, read on an affine chart
-- statement:
--   Let $K$ be a field, let $X$ be a scheme, let $f : X \to \operatorname{Spec} K$ be a morphism that is smooth of relative dimension $n$ for a natural number $n$, let $U$ be an open of $X$ with $U$ affine, and let $e_1 : \operatorname{Spec} K \to U$ be a morphism of schemes into the open subscheme $U$ such that $e_1$ followed by the inclusion $U \hookrightarrow X$ followed by $f$ is the identity of $\operatorname{Spec} K$; thus $e_1$ is a $K$-rational point of $X$ lying in $U$. Equip $\Gamma(X,U)$ with the $K$-algebra structure coming from the ring homomorphism $K \to \Gamma(X,U)$ obtained from the inverse of $\Gamma\!\operatorname{Spec}$-iso followed by $f^{\#}$ on sections over $\top$ restricted to $U$ (the structure `algebraOfHom f U`). Let $\mathrm{ev} : \Gamma(X,U) \to K$ be the ring homomorphism given by the identification $\Gamma(X,U) \cong \Gamma(U,\top)$, followed by $e_1$ on global sections, followed by the canonical isomorphism $\Gamma(\operatorname{Spec} K,\top) \cong K$, and put $\mathfrak m = \ker(\mathrm{ev})$. The conclusion is twofold: first, $\mathrm{ev}$ composed with the structure map $K \to \Gamma(X,U)$ is the identity of $K$, so $\mathrm{ev}$ is an augmentation of the $K$-algebra $\Gamma(X,U)$; second, there exist a $K$-vector space $\Omega$ that is finite over $K$ and a $K$-linear map $\pi$ from $\mathfrak m$, viewed as a $K$-module, onto $\Omega$, surjective, such that for $x \in \mathfrak m$ one has $\pi(x) = 0$ if and only if $x \in \mathfrak m^2$, and $\dim_K \Omega = n$. In other words $\mathfrak m/\mathfrak m^2$ has dimension $n$ over $K$, presented as an abstract quotient rather than as the quotient module itself.
--
--   This transports the computation of the cotangent dimension at a $K$-rational point of a smooth morphism of relative dimension $n$ from the local ring of $X$ at that point, where it is the statement $\dim \mathfrak m_x/\mathfrak m_x^2 = n$ over the residue field, to the coordinate ring of an affine chart containing the point, using that $\mathcal O_{X,x}$ is the localisation of $\Gamma(X,U)$ at $\mathfrak m$ and that localising at a maximal ideal does not change the cotangent space. It is used in the construction of formal coordinates on a deformation, in [`GoodReductionJacobian.BareDeformation.exists_isFormalCoordinates_liftsCoordinates_of_ker_mul_maximalIdeal_eq_bot`](thm.html#GoodReductionJacobian.BareDeformation.exists_isFormalCoordinates_liftsCoordinates_of_ker_mul_maximalIdeal_eq_bot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_finrank_cotangent_chart_eq_of_smoothOfRelativeDimension.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Scheme.TwoAffineOpenCover

theorem AlgebraicGeometry.exists_finrank_cotangent_chart_eq_of_smoothOfRelativeDimension
    {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (U : X.Opens) (hU : IsAffineOpen U)
    (e₁ : Spec (CommRingCat.of K) ⟶ (U : Scheme.{0})) (he₁ : e₁ ≫ U.ι ≫ f = 𝟙 (Spec (CommRingCat.of K))) :
    letI := algebraOfHom f U
    (U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom.comp (algebraMap K Γ(X, U)) = RingHom.id K ∧
    ∃ (Ω : Type) (_ : AddCommGroup Ω) (_ : Module K Ω) (_ : Module.Finite K Ω)
      (π : ↥((RingHom.ker (U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom).restrictScalars K) →ₗ[K] Ω),
      Function.Surjective π ∧
      (∀ x : ↥((RingHom.ker (U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom).restrictScalars K),
        π x = 0 ↔ (x : Γ(X, U)) ∈ (RingHom.ker (U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom) ^ 2) ∧
      Module.finrank K Ω = n := by sorry
