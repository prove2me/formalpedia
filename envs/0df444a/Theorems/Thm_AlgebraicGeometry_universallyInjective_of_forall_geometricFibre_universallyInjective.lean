-- Prove2me | Theorems.Thm_AlgebraicGeometry_universallyInjective_of_forall_geometricFibre_universallyInjective
-- name    : AlgebraicGeometry.universallyInjective_of_forall_geometricFibre_universallyInjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/9252f0e7-78f6-5203-88c7-ebb5225d7ccc
-- title:
--   Universal injectivity from geometric fibres over an affine base
-- statement:
--   Let $S$ be a commutative ring and let $X$, $Y$ be schemes, equipped with morphisms $p : X \to \operatorname{Spec} S$ and $q : Y \to \operatorname{Spec} S$, together with a morphism $\varphi : X \to Y$ over the base, i.e. $\varphi$ followed by $q$ equals $p$. Assume the following hypothesis on geometric fibres: for every algebraically closed field $k$ (in the same universe) and every ring homomorphism $sk : S \to k$ there exist schemes $X'$, $Y'$, morphisms $p' : X' \to \operatorname{Spec} k$, $q' : Y' \to \operatorname{Spec} k$, a morphism $\varphi' : X' \to Y'$ and morphisms $iX : X' \to X$, $iY : Y' \to Y$ such that the squares formed by $(iX, p')$ over $(p, \operatorname{Spec}(sk))$ and by $(iY, q')$ over $(q, \operatorname{Spec}(sk))$ are cartesian, $\varphi'$ followed by $q'$ equals $p'$, the square $iX$ followed by $\varphi$ equals $\varphi'$ followed by $iY$ commutes, and $\varphi'$ is universally injective in the sense of Mathlib's `UniversallyInjective`. The conclusion is that $\varphi$ itself is universally injective. Thus the hypothesis asks for chosen cartesian models of the base changes of $X$ and $Y$ to each geometric point of $\operatorname{Spec} S$, rather than for a property of canonical fibre products.
--
--   This is the descent statement that radicial (universally injective) morphisms over an affine base may be detected on geometric fibres. It is used in the proof that a proper morphism all of whose geometric fibres admit closed-immersion models is a closed immersion, [`AlgebraicGeometry.isClosedImmersion_of_isProper_of_forall_geometricFibre_isClosedImmersion`](thm.html#AlgebraicGeometry.isClosedImmersion_of_isProper_of_forall_geometricFibre_isClosedImmersion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_universallyInjective_of_forall_geometricFibre_universallyInjective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.universallyInjective_of_forall_geometricFibre_universallyInjective
    {S : Type u} [CommRing S] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of S)) (q : Y ⟶ Spec (CommRingCat.of S))
    (φ : X ⟶ Y) (hφ : φ ≫ q = p)
    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k),
      ∃ (X' Y' : Scheme.{u}) (p' : X' ⟶ Spec (CommRingCat.of k)) (q' : Y' ⟶ Spec (CommRingCat.of k))
        (φ' : X' ⟶ Y') (iX : X' ⟶ X) (iY : Y' ⟶ Y),
        IsPullback iX p' p (Spec.map (CommRingCat.ofHom sk)) ∧
        IsPullback iY q' q (Spec.map (CommRingCat.ofHom sk)) ∧
        φ' ≫ q' = p' ∧ iX ≫ φ = φ' ≫ iY ∧ UniversallyInjective φ') :
    UniversallyInjective φ := by sorry
