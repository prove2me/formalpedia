-- Prove2me | Theorems.Thm_CategoryTheory_Abelian_Ext_surjective_levelDelta_app
-- name    : CategoryTheory.Abelian.Ext.surjective_levelDelta_app
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T19:16:06.144735+00:00
-- url     : https://prove2.me/theorems/45ad82e4-6b20-45ad-9ad6-866aafcdfbda
-- title:
--   The levelwise connecting map of the covariant Ext sequence is surjective when the next Ext group of the middle term vanishes
-- statement:
--   Let $\mathcal{A}$ be an abelian category with Ext groups (valued in a universe $w$), let $Z \in \mathcal{A}$, and let
--   $$0 \to X_1 \to X_2 \to X_3 \to 0$$
--   be a short complex of inverse systems $\mathbb{N}^{\mathrm{op}} \to \mathcal{A}$ which is short exact at every level. Fix $i \in \mathbb{N}$ and a level $k$, and let
--   $$\delta_k : \operatorname{Ext}^i(Z, X_3(k)) \to \operatorname{Ext}^{i+1}(Z, X_1(k))$$
--   be the connecting map of the level-$k$ covariant long exact Ext sequence. If $\operatorname{Ext}^{i+1}(Z, X_2(k)) = 0$, then $\delta_k$ is surjective.
--
--   This is the standard dimension-shifting input (e.g. when $X_2$ is levelwise injective), used to compare Ext into a sequential limit with the limit of levelwise Ext groups.
--
--   **Formalization Note** The vanishing hypothesis is `Subsingleton (Ext Z (SC.X₂.obj k) (i + 1))`, and $\delta_k$ is the component `(levelDelta Z hSCk i).app k`. Only `[Abelian A]` and `[HasExt.{w} A]` are assumed; the section variables `HasExt (ℕᵒᵖ ⥤ A)`, `EnoughInjectives A` and `HasProductsOfShape ℕ A` are omitted. The theorem is `CategoryTheory.Abelian.Ext.surjective_levelDelta_app`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Algebra/Homology/DerivedCategory/Ext/SequentialLimit.lean, lines 708-717 (`CategoryTheory.Abelian.Ext.surjective_levelDelta_app`).

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

theorem surjective_levelDelta_app
    (hSCk : ∀ k : ℕᵒᵖ, (SC.map ((evaluation ℕᵒᵖ A).obj k)).ShortExact) (i : ℕ) (k : ℕᵒᵖ)
    (h₂ : Subsingleton (Ext Z (SC.X₂.obj k) (i + 1))) :
    Function.Surjective (ConcreteCategory.hom ((levelDelta Z hSCk i).app k)) := by sorry

end Main

end Ext
end Abelian
end CategoryTheory
