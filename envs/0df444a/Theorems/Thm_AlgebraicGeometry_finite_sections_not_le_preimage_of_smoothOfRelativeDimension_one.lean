-- Prove2me | Theorems.Thm_AlgebraicGeometry_finite_sections_not_le_preimage_of_smoothOfRelativeDimension_one
-- name    : AlgebraicGeometry.finite_sections_not_le_preimage_of_smoothOfRelativeDimension_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/71b9af3f-7342-5999-a01a-4ea53066f295
-- title:
--   Finitely many L-points off a non-empty open of a curve
-- statement:
--   Let $L$ be a field and let $X$ be a scheme over the universe level in question which is integral, equipped with a morphism $c : X \to \operatorname{Spec} L$ that is quasi-compact and smooth of relative dimension $1$. Let $U$ be an open subscheme of $X$ whose underlying set is non-empty. The assertion is that the set of morphisms $q : \operatorname{Spec} L \to X$ satisfying the two conditions that $q$ followed by $c$ is the identity of $\operatorname{Spec} L$ (that is, $q$ is a section of $c$, equivalently an $L$-rational point of $X$) and that the open subscheme $q^{-1}U$ of $\operatorname{Spec} L$ is not the whole of $\operatorname{Spec} L$ (equivalently, since $\operatorname{Spec} L$ has a single point, the image point of $q$ does not lie in $U$) is a finite set. Thus only finitely many $L$-points of $X$ avoid $U$.
--
--   This is the standard finiteness statement that on an integral curve, smooth of relative dimension one and quasi-compact over a field, a non-empty open subset omits only finitely many rational points. It is used in the Čerednik–Drinfel'd part of the development, in [`CerednikDrinfeld.finite_affinoid_toOmega_of_not_le_preimage_of_cerednikDrinfeld_quotient_of_smooth`](thm.html#CerednikDrinfeld.finite_affinoid_toOmega_of_not_le_preimage_of_cerednikDrinfeld_quotient_of_smooth).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_finite_sections_not_le_preimage_of_smoothOfRelativeDimension_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.finite_sections_not_le_preimage_of_smoothOfRelativeDimension_one
    {L : Type u} [Field L] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of L))
    [IsIntegral X] [SmoothOfRelativeDimension 1 c] [QuasiCompact c]
    (U : X.Opens) (hU : (U : Set X).Nonempty) :
    Set.Finite {q : Spec (CommRingCat.of L) ⟶ X |
      q ≫ c = 𝟙 (Spec (CommRingCat.of L)) ∧ ¬ ((⊤ : (Spec (CommRingCat.of L)).Opens) ≤ q ⁻¹ᵁ U)} := by sorry
