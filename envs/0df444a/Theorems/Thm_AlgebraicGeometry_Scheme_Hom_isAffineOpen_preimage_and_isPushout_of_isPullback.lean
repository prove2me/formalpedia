-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isAffineOpen_preimage_and_isPushout_of_isPullback
-- name    : AlgebraicGeometry.Scheme.Hom.isAffineOpen_preimage_and_isPushout_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/f3b2750a-8a50-504b-ba30-8d8639c1057f
-- title:
--   Base change over affine bases: affine charts and sections as pushout
-- statement:
--   Let $A$ and $B$ be commutative rings with $B$ an $A$-algebra, let $X$ and $Y$ be schemes, and let $gY : Y \to \operatorname{Spec} A$, $gX : X \to \operatorname{Spec} B$ and $\varphi : X \to Y$ be morphisms such that the square formed by $\varphi$, $gX$, $gY$ and $\operatorname{Spec}$ of the structure map $A \to B$ is cartesian, i.e. $X$ together with $\varphi$ and $gX$ is a pullback of $Y \to \operatorname{Spec} A \leftarrow \operatorname{Spec} B$. Let $U \subseteq Y$ be an open subscheme which is an affine open. The conclusion is twofold: first, the open $\varphi^{-1}U \subseteq X$ is again an affine open; second, consider the algebra structures given by `sectionsAlgebra`, namely the $A$-algebra structure on $\Gamma(Y,U)$ induced by the ring map $\Gamma(\operatorname{Spec} A, \top) \cong A \to \Gamma(Y,U)$ coming from $gY$ (its `appLE ⊤ U`), the $B$-algebra structure on $\Gamma(X, \varphi^{-1}U)$ induced in the same way from $gX$, and the $\Gamma(Y,U)$-algebra structure on $\Gamma(X,\varphi^{-1}U)$ given by $\varphi$ on sections over $U$ and $\varphi^{-1}U$; then for every $A$-algebra structure on $\Gamma(X,\varphi^{-1}U)$ compatible with both towers $A \to B \to \Gamma(X,\varphi^{-1}U)$ and $A \to \Gamma(Y,U) \to \Gamma(X,\varphi^{-1}U)$, one has `Algebra.IsPushout A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U)`, i.e. $B \otimes_A \Gamma(Y,U) \to \Gamma(X,\varphi^{-1}U)$ is bijective.
--
--   This is the standard description of a base change along an affine base in charts: over an affine open $U$ of $Y$ the fibre product is $\operatorname{Spec}(B \otimes_A \Gamma(Y,U))$. It is used in the scheme-theoretic infrastructure of the project, for instance when comparing modules and their pullbacks over affine charts and when checking that a morphism of pullbacks is an isomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_isAffineOpen_preimage_and_isPushout_of_isPullback.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_KaehlerModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

theorem AlgebraicGeometry.Scheme.Hom.isAffineOpen_preimage_and_isPushout_of_isPullback
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of B))
    (φ : X ⟶ Y) (hφ : IsPullback φ gX gY (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (U : Y.Opens) (hU : IsAffineOpen U) :
    IsAffineOpen (φ ⁻¹ᵁ U) ∧
      letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra (φ ⁻¹ᵁ U)
      letI : Algebra Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := (φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom.toAlgebra
      ∀ [Algebra A Γ(X, φ ⁻¹ᵁ U)] [IsScalarTower A B Γ(X, φ ⁻¹ᵁ U)]
        [IsScalarTower A Γ(Y, U) Γ(X, φ ⁻¹ᵁ U)],
        Algebra.IsPushout A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := by sorry
