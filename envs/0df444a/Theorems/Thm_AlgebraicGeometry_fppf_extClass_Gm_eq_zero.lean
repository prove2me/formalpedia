-- Prove2me | Theorems.Thm_AlgebraicGeometry_fppf_extClass_Gm_eq_zero
-- name    : AlgebraicGeometry.fppf_extClass_Gm_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/ba6ccba9-8021-5b8b-9207-f20ecfb2f824
-- title:
--   Splitting of fppf extensions of underlineℤ by mathbb G_m
-- statement:
--   Work on the site of schemes in the lowest universe equipped with the fppf topology, with sheaves valued in additive commutative groups. Let $E$ be such a sheaf, valued in `AddCommGrpCat.{1}`, and let [`FppfKummerSES.GmAbelianSheafLifted`](def/AlgebraicGeometry_FppfKummerProp17.html#L387) denote the fppf sheaf represented by the multiplicative group scheme $\mathbb G_m$, transported from commutative groups to additive commutative groups by the standard equivalence and then lifted one universe level by the functor `AddCommGrpCat.uliftFunctor` applied termwise. Given a morphism $f$ from this lifted $\mathbb G_m$-sheaf to $E$, a morphism $g$ from $E$ to the constant fppf sheaf with value `ULift ℤ`, and a proof $w$ that the composite of $f$ followed by $g$ is zero, form the short complex with these data. Assuming this short complex is short exact in the abelian category of such sheaves, the assertion is that its associated extension class, the element of $\operatorname{Ext}^1$ of the constant sheaf $\underline{\mathbb Z}$ by the lifted $\mathbb G_m$ given by `ShortComplex.ShortExact.extClass`, is zero; equivalently, the extension splits.
--
--   This is the statement that $\operatorname{Pic}(\operatorname{Spec}\mathbb Z)=0$ in the language of extension classes of fppf abelian sheaves: every extension of $\underline{\mathbb Z}$ by $\mathbb G_m$ on the absolute fppf site is split. It is used in the proof that the first fppf cohomology group of $\mathbb G_m$ over $\operatorname{Spec}\mathbb Z$ is trivial ([`AlgebraicGeometry.subsingleton_fppfH1_Gm_specZ`](thm.html#AlgebraicGeometry.subsingleton_fppfH1_Gm_specZ)), part of the Kummer-sequence input to the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_fppf_extClass_Gm_eq_zero.lean

import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Abelian Limits AlgebraicGeometry

theorem AlgebraicGeometry.fppf_extClass_Gm_eq_zero
    (E : CategoryTheory.Sheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1})
    (f : FppfKummerSES.GmAbelianSheafLifted.{0} ⟶ E)
    (g : E ⟶ (CategoryTheory.constantSheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}).obj (.of (ULift.{1} ℤ)))
    (w : f ≫ g = 0)
    (hS : (CategoryTheory.ShortComplex.mk f g w).ShortExact) :
    hS.extClass = 0 := by sorry
