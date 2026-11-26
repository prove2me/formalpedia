-- Prove2me | Theorems.Thm_CategoryTheory_Abelian_Ext_levelDelta_comp_app_zero
-- name    : CategoryTheory.Abelian.Ext.levelDelta_comp_app_zero
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T19:15:41.579806+00:00
-- url     : https://prove2.me/theorems/87d9a89b-0b3b-540c-b73a-02698e5cd563
-- title:
--   The levelwise connecting map of the covariant Ext sequence kills the image of the middle term
-- statement:
--   Let $\mathcal{A}$ be an abelian category with Ext groups (valued in a universe $w$), let $Z \in \mathcal{A}$, and let
--   $$0 \to X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3 \to 0$$
--   be a short complex of inverse systems $\mathbb{N}^{\mathrm{op}} \to \mathcal{A}$ which is short exact at every level $k$. Let $\delta_k : \operatorname{Ext}^i(Z, X_3(k)) \to \operatorname{Ext}^{i+1}(Z, X_1(k))$ be the connecting map of the level-$k$ covariant long exact Ext sequence, and $g_{k,*} : \operatorname{Ext}^i(Z, X_2(k)) \to \operatorname{Ext}^i(Z, X_3(k))$ composition with $g_k$. Then for every $b \in \operatorname{Ext}^i(Z, X_2(k))$,
--   $$\delta_k\big(g_{k,*}(b)\big) = 0.$$
--
--   Together with its converse (classes killed by $\delta_k$ come from $X_2(k)$) this expresses levelwise exactness of the long exact sequence at the third term, used in dimension-shifting arguments for Ext into sequential limits.
--
--   **Formalization Note** The connecting maps form the morphism of systems `levelDelta Z hSCk i`, and $g_{k,*}$ is the component at $k$ of `Functor.whiskerRight SC.g (extFunctorObj Z i)`. Only `[Abelian A]` and `[HasExt.{w} A]` are assumed; the section variables `HasExt (ℕᵒᵖ ⥤ A)`, `EnoughInjectives A` and `HasProductsOfShape ℕ A` are omitted. The theorem is `CategoryTheory.Abelian.Ext.levelDelta_comp_app_zero`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Algebra/Homology/DerivedCategory/Ext/SequentialLimit.lean, lines 679-692 (`CategoryTheory.Abelian.Ext.levelDelta_comp_app_zero`).

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

theorem levelDelta_comp_app_zero
    (hSCk : ∀ k : ℕᵒᵖ, (SC.map ((evaluation ℕᵒᵖ A).obj k)).ShortExact) (i : ℕ) (k : ℕᵒᵖ)
    (b : Ext Z (SC.X₂.obj k) i) :
    ConcreteCategory.hom ((levelDelta Z hSCk i).app k)
      (ConcreteCategory.hom ((Functor.whiskerRight SC.g (extFunctorObj Z i)).app k) b) =
      0 := by sorry

end Main

end Ext
end Abelian
end CategoryTheory
