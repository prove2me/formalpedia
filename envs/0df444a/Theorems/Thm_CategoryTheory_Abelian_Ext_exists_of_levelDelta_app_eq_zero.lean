-- Prove2me | Theorems.Thm_CategoryTheory_Abelian_Ext_exists_of_levelDelta_app_eq_zero
-- name    : CategoryTheory.Abelian.Ext.exists_of_levelDelta_app_eq_zero
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T19:15:58.048364+00:00
-- url     : https://prove2.me/theorems/c5a3e8a7-2f54-4b95-8346-234bd935d682
-- title:
--   Levelwise exactness of the covariant Ext sequence at the third term: classes killed by the connecting map come from the middle term
-- statement:
--   Let $\mathcal{A}$ be an abelian category with Ext groups (valued in a universe $w$), let $Z \in \mathcal{A}$, and let
--   $$0 \to X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3 \to 0$$
--   be a short complex of inverse systems $\mathbb{N}^{\mathrm{op}} \to \mathcal{A}$ which is short exact at every level $k$. For each $k$ and $i$ let
--   $$\delta_k : \operatorname{Ext}^i(Z, X_3(k)) \to \operatorname{Ext}^{i+1}(Z, X_1(k))$$
--   be the connecting map of the covariant long exact Ext sequence at level $k$ (composition with the extension class of the level-$k$ short exact sequence). If $c \in \operatorname{Ext}^i(Z, X_3(k))$ satisfies $\delta_k(c) = 0$, then there is $b \in \operatorname{Ext}^i(Z, X_2(k))$ with
--   $$g_{k,*}(b) = c,$$
--   where $g_{k,*}$ is composition with $g_k : X_2(k) \to X_3(k)$.
--
--   This is one of the levelwise exactness statements used for dimension shifting when comparing Ext into a sequential limit with the limit of the levelwise Ext groups.
--
--   **Formalization Note** The connecting maps assemble into a morphism of inverse systems `levelDelta Z hSCk i`, and the theorem concerns its component `.app k`; $g_{k,*}$ is the component of `Functor.whiskerRight SC.g (extFunctorObj Z i)`. Only `[Abelian A]` and `[HasExt.{w} A]` are assumed; the section variables `HasExt (ℕᵒᵖ ⥤ A)`, `EnoughInjectives A` and `HasProductsOfShape ℕ A` are omitted. The theorem is `CategoryTheory.Abelian.Ext.exists_of_levelDelta_app_eq_zero`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Algebra/Homology/DerivedCategory/Ext/SequentialLimit.lean, lines 694-706 (`CategoryTheory.Abelian.Ext.exists_of_levelDelta_app_eq_zero`).

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

section Main

variable [EnoughInjectives A] [HasProductsOfShape ℕ A]

variable (Z : A)

variable {SC : ShortComplex (ℕᵒᵖ ⥤ A)}

omit [HasExt.{w} (ℕᵒᵖ ⥤ A)] [EnoughInjectives A] [HasProductsOfShape ℕ A] in

theorem exists_of_levelDelta_app_eq_zero
    (hSCk : ∀ k : ℕᵒᵖ, (SC.map ((evaluation ℕᵒᵖ A).obj k)).ShortExact) (i : ℕ) (k : ℕᵒᵖ)
    (c : Ext Z (SC.X₃.obj k) i)
    (hc : ConcreteCategory.hom ((levelDelta Z hSCk i).app k) c = 0) :
    ∃ b : Ext Z (SC.X₂.obj k) i,
      ConcreteCategory.hom ((Functor.whiskerRight SC.g (extFunctorObj Z i)).app k) b =
        c := by sorry

end Main

end Ext
end Abelian
end CategoryTheory
