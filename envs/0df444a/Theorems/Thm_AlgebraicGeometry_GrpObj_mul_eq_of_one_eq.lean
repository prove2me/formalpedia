-- Prove2me | Theorems.Thm_AlgebraicGeometry_GrpObj_mul_eq_of_one_eq
-- name    : AlgebraicGeometry.GrpObj.mul_eq_of_one_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/6cc7ac39-be86-5367-a25e-5910f2606da3
-- title:
--   A group object on a proper integral scheme is determined by its unit
-- statement:
--   Let $K$ be an algebraically closed field, $X$ a scheme, and $x : X \to \operatorname{Spec} K$ a structure morphism which is proper, with $X$ integral and with the fibre product $X \times_{x,x} X$ (the Mathlib pullback of $x$ along itself) reduced. Consider the object $\mathrm{Over.mk}\,x$ of the slice category of schemes over $\operatorname{Spec} K$, which is cartesian monoidal, so that its tensor product is the fibre product over $\operatorname{Spec} K$ and its unit is $\operatorname{Spec} K$ itself. Let $G_1$ and $G_2$ be two group-object structures on $\mathrm{Over.mk}\,x$, each consisting of a multiplication $X \times_K X \to X$, a unit section $\operatorname{Spec} K \to X$ and an inverse $X \to X$ over $\operatorname{Spec} K$ satisfying the group-object axioms. The assertion is: if the two unit morphisms agree, $G_1.\mathrm{one} = G_2.\mathrm{one}$, then the two multiplications agree, $G_1.\mathrm{mul} = G_2.\mathrm{mul}$, as morphisms $\mathrm{Over.mk}\,x \otimes \mathrm{Over.mk}\,x \to \mathrm{Over.mk}\,x$. Equality of the inverses is not part of the conclusion (it follows formally from equality of multiplication and unit).
--
--   This is the rigidity statement that a group scheme structure on a proper integral scheme over an algebraically closed field is determined by its unit section, in the form used for abelian varieties (cf. Mumford, Abelian Varieties, §4). It is used to show that the relative group law on a Weierstrass projective model is the unique one with the given identity section, via [`WeierstrassProjModel.RelativeGroupLaw.mul_eq_at_id_of_one_eq_at_id_of_isAlgClosed`](thm.html#WeierstrassProjModel.RelativeGroupLaw.mul_eq_at_id_of_one_eq_at_id_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_GrpObj_mul_eq_of_one_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.GrpObj.mul_eq_of_one_eq
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of K)) [IsProper x] [IsIntegral X]
    [IsReduced (CategoryTheory.Limits.pullback x x)]
    (G₁ G₂ : GrpObj (Over.mk x)) (h : G₁.one = G₂.one) : G₁.mul = G₂.mul := by sorry
