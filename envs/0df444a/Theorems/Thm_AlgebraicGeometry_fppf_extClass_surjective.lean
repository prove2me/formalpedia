-- Prove2me | Theorems.Thm_AlgebraicGeometry_fppf_extClass_surjective
-- name    : AlgebraicGeometry.fppf_extClass_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/f810d964-c2d2-5262-916f-43eb1cb68801
-- title:
--   Every Ext¹ class of fppf sheaves comes from an extension
-- statement:
--   Let $F$ be a sheaf of abelian groups on the big fppf site of schemes, that is, an object of `CategoryTheory.Sheaf Scheme.fppfTopology AddCommGrpCat`, the schemes being taken in universe $0$ and the abelian groups in universe $1$, and write $\underline{\mathbb Z}$ for the sheaf $\mathrm{constantSheaf}(\mathbb Z)$ obtained by applying the constant-sheaf functor for the fppf topology to the additive group `ULift ℤ`. Let $e$ be an element of $\operatorname{Ext}^1(\underline{\mathbb Z}, F)$, the degree-one Ext group of Mathlib's `CategoryTheory.Abelian.Ext` in this abelian category. The assertion is that there exist an abelian fppf sheaf $E$, morphisms $f : F \to E$ and $g : E \to \underline{\mathbb Z}$, a proof $w$ that $f$ followed by $g$ is zero, and a proof $hS$ that the resulting short complex $0 \to F \xrightarrow{f} E \xrightarrow{g} \underline{\mathbb Z} \to 0$ is short exact, such that the extension class `hS.extClass` of this short exact sequence, an element of $\operatorname{Ext}^1(\underline{\mathbb Z}, F)$, equals $e$. Thus the extension-class map is surjective in this particular pair of objects; no further hypothesis on $F$ or $e$ is imposed.
--
--   This is the surjectivity half of the Yoneda description of $\operatorname{Ext}^1$ as a group of extension classes, specialised to abelian sheaves on the big fppf site, where $\operatorname{Ext}^1(\underline{\mathbb Z}, F)$ is the first fppf cohomology group of $F$. It is used in the computations of first fppf cohomology over $\operatorname{Spec}\mathbb Z$, namely [`AlgebraicGeometry.subsingleton_fppfH1_Gm_specZ`](thm.html#AlgebraicGeometry.subsingleton_fppfH1_Gm_specZ) and [`AlgebraicGeometry.subsingleton_fppfH1_constantZMod_specZ_of_prime`](thm.html#AlgebraicGeometry.subsingleton_fppfH1_constantZMod_specZ_of_prime), which deduce the vanishing of $H^1$ from the splitting of all such extensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_fppf_extClass_surjective.lean

import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Abelian Limits AlgebraicGeometry

theorem AlgebraicGeometry.fppf_extClass_surjective
    (F : CategoryTheory.Sheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1})
    (e : CategoryTheory.Abelian.Ext
      ((CategoryTheory.constantSheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}).obj
        (.of (ULift.{1} ℤ))) F 1) :
    ∃ (E : CategoryTheory.Sheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1})
      (f : F ⟶ E)
      (g : E ⟶ (CategoryTheory.constantSheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}).obj
        (.of (ULift.{1} ℤ)))
      (w : f ≫ g = 0)
      (hS : (CategoryTheory.ShortComplex.mk f g w).ShortExact),
      hS.extClass = e := by sorry
