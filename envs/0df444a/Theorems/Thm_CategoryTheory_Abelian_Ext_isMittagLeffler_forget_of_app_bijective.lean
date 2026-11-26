-- Prove2me | Theorems.Thm_CategoryTheory_Abelian_Ext_isMittagLeffler_forget_of_app_bijective
-- name    : CategoryTheory.Abelian.Ext.isMittagLeffler_forget_of_app_bijective
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T19:16:09.10037+00:00
-- url     : https://prove2.me/theorems/7fef19c0-69a9-4cfd-871f-4919cc167f6c
-- title:
--   The Mittag-Leffler condition descends along a levelwise bijective morphism of inverse sequences of abelian groups
-- statement:
--   Let $C$ and $D$ be inverse sequences of abelian groups (functors $\mathbb{N}^{\mathrm{op}} \to \mathbf{Ab}$) and let $\varphi : C \to D$ be a morphism of inverse systems such that every component $\varphi_k : C_k \to D_k$ is bijective. If the underlying inverse system of sets of $D$ satisfies the Mittag-Leffler condition, then so does the underlying inverse system of sets of $C$.
--
--   Recall that an inverse sequence $(X_n)$ is Mittag-Leffler if for every $n$ there is $m \ge n$ such that the image of $X_k \to X_n$ contains the image of $X_m \to X_n$ for all $k \ge n$. The lemma lets one transport the Mittag-Leffler hypothesis between isomorphic descriptions of systems of Ext groups.
--
--   **Formalization Note** The groups live in `AddCommGrpCat.{w}`; the Mittag-Leffler condition is Mathlib's `Functor.IsMittagLeffler`, applied to the composite with `forget AddCommGrpCat`. Although stated in a namespace with section variables about an abelian category `A`, the statement does not use them. The theorem is `CategoryTheory.Abelian.Ext.isMittagLeffler_forget_of_app_bijective`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Algebra/Homology/DerivedCategory/Ext/SequentialLimit.lean, lines 313-340 (`CategoryTheory.Abelian.Ext.isMittagLeffler_forget_of_app_bijective`).

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

theorem isMittagLeffler_forget_of_app_bijective {C D : ℕᵒᵖ ⥤ AddCommGrpCat.{w}}
    (φ : C ⟶ D) (hφ : ∀ k, Function.Bijective (ConcreteCategory.hom (φ.app k)))
    (hD : (D ⋙ CategoryTheory.forget AddCommGrpCat.{w}).IsMittagLeffler) :
    (C ⋙ CategoryTheory.forget AddCommGrpCat.{w}).IsMittagLeffler := by sorry

end AbChase

end Ext
end Abelian
end CategoryTheory
