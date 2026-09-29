-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsPullback_surjective_app_and_ker_app_eq_map_ker_of_isAffineOpen
-- name    : AlgebraicGeometry.IsPullback.surjective_app_and_ker_app_eq_map_ker_of_isAffineOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/3e3cd5af-4753-5d97-945f-e89c36212c9a
-- title:
--   Affine opens of a nil-thickening: sections surject with kernel JΓ
-- statement:
--   Let $T'$ and $T$ be commutative rings and let $\pi \colon T' \to T$ be a ring homomorphism which is surjective and whose kernel ideal $\ker \pi$ is nilpotent (some power of it vanishes). Let $P$ and $P_0$ be schemes equipped with morphisms $p \colon P \to \operatorname{Spec} T'$ and $p_0 \colon P_0 \to \operatorname{Spec} T$, and let $G \colon P_0 \to P$ be a morphism such that the square formed by $G$, $p_0$, $p$ and $\operatorname{Spec} \pi$ is commutative and cartesian, in the sense that $G$ followed by $p$ equals $p_0$ followed by $\operatorname{Spec} \pi$ and this square is a pullback. Let $D$ be an open subscheme of $P$ which is an affine open. Give $\Gamma(P, D)$ the $T'$-algebra structure coming from $p$, namely the ring map $T' \to \Gamma(P,D)$ obtained by composing the inverse of the $\Gamma$–$\operatorname{Spec}$ isomorphism for $T'$ with the restriction $p^{\sharp} \colon \Gamma(\operatorname{Spec} T', \top) \to \Gamma(P, D)$ of $p$ over $D$. Then the induced ring map on sections $G^{\sharp}_D \colon \Gamma(P, D) \to \Gamma(P_0, G^{-1}D)$ is surjective, and its kernel is exactly the ideal $(\ker \pi)\,\Gamma(P,D)$, the image ideal of $\ker \pi$ under the structure map $T' \to \Gamma(P,D)$.
--
--   This is the local description of the base change of a scheme along a surjection with nilpotent kernel: over an affine open $D$ of $P$, the preimage $G^{-1}D$ has coordinate ring $\Gamma(P,D) \otimes_{T'} T = \Gamma(P,D)/(\ker\pi)\Gamma(P,D)$ and $G$ acts on sections as the corresponding quotient map. It is used in the deformation-theoretic analysis of line bundles on a nil-thickening, in particular in the construction and comparison of Picard cocycles for small extensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsPullback_surjective_app_and_ker_app_eq_map_ker_of_isAffineOpen.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.IsPullback.surjective_app_and_ker_app_eq_map_ker_of_isAffineOpen
    {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {P P₀ : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of T')) (p₀ : P₀ ⟶ Spec (CommRingCat.of T))
    (G : P₀ ⟶ P) (hG : IsPullback G p₀ p (Spec.map (CommRingCat.ofHom π)))
    (D : P.Opens) (hD : IsAffineOpen D) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p D
    Function.Surjective (G.app D).hom ∧
      RingHom.ker (G.app D).hom = (RingHom.ker π).map (algebraMap T' Γ(P, D)) := by sorry
