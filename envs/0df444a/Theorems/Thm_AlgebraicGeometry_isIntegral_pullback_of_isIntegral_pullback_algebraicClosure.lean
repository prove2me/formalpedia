-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIntegral_pullback_of_isIntegral_pullback_algebraicClosure
-- name    : AlgebraicGeometry.isIntegral_pullback_of_isIntegral_pullback_algebraicClosure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/c7ae1017-19ae-5f4a-bb32-a0da17a60aa8
-- title:
--   Integrality descends from K̄ to K
-- statement:
--   Let $R$ be a commutative ring, let $X$ be a scheme and let $f \colon X \to \operatorname{Spec} R$ be a morphism of schemes, and let $K$ be a field carrying an $R$-algebra structure. Write $\operatorname{Spec} K \to \operatorname{Spec} R$ for the morphism obtained by applying $\operatorname{Spec}$ to the structure map $R \to K$, and $\operatorname{Spec} \overline{K} \to \operatorname{Spec} R$ for the morphism obtained from the composite $R \to K \to \overline{K}$, where $\overline{K}$ is the algebraic closure of $K$ produced by `AlgebraicClosure`. The hypothesis is that the fibre product of $f$ with $\operatorname{Spec} \overline{K} \to \operatorname{Spec} R$, that is $X \times_{\operatorname{Spec} R} \operatorname{Spec}\overline{K}$, is an integral scheme in the sense of Mathlib's `AlgebraicGeometry.IsIntegral`, i.e. its underlying space is irreducible and it is reduced. The conclusion is that the fibre product of $f$ with $\operatorname{Spec} K \to \operatorname{Spec} R$, that is $X \times_{\operatorname{Spec} R} \operatorname{Spec} K$, is likewise integral. Thus integrality of a base change to a field descends from the algebraic closure of that field to the field itself.
--
--   This is the standard descent of integrality along the faithfully flat, surjective morphism $\operatorname{Spec}\overline{K} \to \operatorname{Spec} K$, which permits a question of integrality of a fibre to be checked after passing to an algebraically closed field. It is used for the integrality of the pullbacks of the Igusa scheme morphism in characteristic zero and in positive characteristic, and in the construction of an integral coarse moduli scheme in the Čerednik–Drinfel'd setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIntegral_pullback_of_isIntegral_pullback_algebraicClosure.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section
set_option autoImplicit false

theorem AlgebraicGeometry.isIntegral_pullback_of_isIntegral_pullback_algebraicClosure
    {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (K : Type) [Field K] [Algebra R K]
    (h : IsIntegral ↑(pullback f (Spec.map (CommRingCat.ofHom
      ((algebraMap K (AlgebraicClosure K)).comp (algebraMap R K)))))) :
    IsIntegral ↑(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := by sorry
