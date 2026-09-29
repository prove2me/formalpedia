-- Prove2me | Theorems.Thm_AlgebraicGeometry_isClosedImmersion_of_isProper_of_forall_geometricFibre_isClosedImmersion
-- name    : AlgebraicGeometry.isClosedImmersion_of_isProper_of_forall_geometricFibre_isClosedImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/c7c62bbf-dcee-52f0-a4c2-ddaff87959be
-- title:
--   Proper over a base and closed immersion on geometric fibres
-- statement:
--   Let $S$ be a commutative ring and let $X$, $Y$ be schemes. Let $p : X \to \operatorname{Spec} S$ be proper, let $q : Y \to \operatorname{Spec} S$ be separated, and let $\varphi : X \to Y$ be a morphism over $S$, in the sense that $\varphi$ followed by $q$ equals $p$. Assume the following fibrewise condition: for every algebraically closed field $k$ (a type in the same universe) and every ring homomorphism $s_k : S \to k$ there exist schemes $X'$, $Y'$, morphisms $p' : X' \to \operatorname{Spec} k$, $q' : Y' \to \operatorname{Spec} k$, $\varphi' : X' \to Y'$, $i_X : X' \to X$ and $i_Y : Y' \to Y$ such that the square formed by $i_X, p'$ and $p, \operatorname{Spec}(s_k)$ is a pullback square, the square formed by $i_Y, q'$ and $q, \operatorname{Spec}(s_k)$ is a pullback square, $\varphi'$ followed by $q'$ equals $p'$, $i_X$ followed by $\varphi$ equals $\varphi'$ followed by $i_Y$, and $\varphi'$ is a closed immersion. Then $\varphi$ is a closed immersion. Thus the geometric fibres are presented as arbitrary chosen pullbacks compatible with $\varphi$, rather than as a fixed construction of the base change.
--
--   This is the standard criterion (EGA IV 18.12.6 in the form used in practice) that a morphism between an $S$-proper scheme and an $S$-separated scheme which is a closed immersion on all geometric fibres is itself a closed immersion. It is used in the treatment of good reduction of Jacobians, where a family of sections is shown to define a closed immersion of abelian schemes by checking the assertion fibre by fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isClosedImmersion_of_isProper_of_forall_geometricFibre_isClosedImmersion.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isClosedImmersion_of_isProper_of_forall_geometricFibre_isClosedImmersion
    {S : Type u} [CommRing S] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of S)) [IsProper p]
    (q : Y ⟶ Spec (CommRingCat.of S)) [IsSeparated q]
    (φ : X ⟶ Y) (hφ : φ ≫ q = p)
    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k),
      ∃ (X' Y' : Scheme.{u}) (p' : X' ⟶ Spec (CommRingCat.of k)) (q' : Y' ⟶ Spec (CommRingCat.of k))
        (φ' : X' ⟶ Y') (iX : X' ⟶ X) (iY : Y' ⟶ Y),
        IsPullback iX p' p (Spec.map (CommRingCat.ofHom sk)) ∧
        IsPullback iY q' q (Spec.map (CommRingCat.ofHom sk)) ∧
        φ' ≫ q' = p' ∧ iX ≫ φ = φ' ≫ iY ∧ IsClosedImmersion φ') :
    IsClosedImmersion φ := by sorry
