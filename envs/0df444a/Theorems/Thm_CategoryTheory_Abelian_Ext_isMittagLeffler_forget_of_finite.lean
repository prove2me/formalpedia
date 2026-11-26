-- Prove2me | Theorems.Thm_CategoryTheory_Abelian_Ext_isMittagLeffler_forget_of_finite
-- name    : CategoryTheory.Abelian.Ext.isMittagLeffler_forget_of_finite
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T19:16:17.281681+00:00
-- url     : https://prove2.me/theorems/a1159a8f-f87f-49a8-b986-6c25730150a2
-- title:
--   An inverse system of finite abelian groups satisfies the Mittag-Leffler condition
-- statement:
--   Let $(C_n)_{n\in\mathbb N}$ be an inverse system of abelian groups (a functor $\mathbb N^{\mathrm{op}}\to\mathbf{Ab}$) such that every $C_n$ is finite. Then the underlying inverse system of sets satisfies the Mittag-Leffler condition: for every $n$, the images
--   $$\operatorname{im}\big(C_m \to C_n\big), \qquad m\ge n,$$
--   form a decreasing family of subsets that is eventually constant.
--
--   This standard fact is used to verify the Mittag-Leffler hypotheses in the comparison of Ext groups into a limit with the limit of Ext groups, e.g. when the groups involved are finite cohomology groups with $\mathbb Z/\ell^n$ coefficients.
--
--   **Formalization Note** `C : ℕᵒᵖ ⥤ AddCommGrpCat.{w}` with `Finite (ToType (C.obj (op n)))` for every `n`. The conclusion is Mathlib's `Functor.IsMittagLeffler` for `C ⋙ forget AddCommGrpCat`, whose definition is that for each index the images of the maps from all further indices stabilize; the description of that predicate above is from Mathlib's definition.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Algebra/Homology/DerivedCategory/Ext/SequentialLimit.lean, lines 305-311 (`CategoryTheory.Abelian.Ext.isMittagLeffler_forget_of_finite`).

import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Definitions.Def_ProEtale_Mathlib_Algebra_Homology_DerivedCategory_Ext_Product
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Abelian_SequentialSystem
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Abelian_SequentialSystem_Lib
import Definitions.Def_ProEtale_Mathlib_Algebra_Homology_DerivedCategory_Ext_SequentialLimit

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

universe w t v u

open CategoryTheory Limits Opposite

namespace CategoryTheory
namespace Abelian
namespace Ext

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A] [HasExt.{w} (ℕᵒᵖ ⥤ A)]

section AbChase

variable {B C D : ℕᵒᵖ ⥤ AddCommGrpCat.{w}} (g : B ⟶ C) (h : C ⟶ D)

theorem isMittagLeffler_forget_of_finite (C : ℕᵒᵖ ⥤ AddCommGrpCat.{w})
    (hC : ∀ n : ℕ, Finite (ToType (C.obj (op n)))) :
    (C ⋙ CategoryTheory.forget AddCommGrpCat.{w}).IsMittagLeffler := by sorry

end AbChase

end Ext
end Abelian
end CategoryTheory
