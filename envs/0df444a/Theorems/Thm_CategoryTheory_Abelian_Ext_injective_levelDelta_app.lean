-- Prove2me | Theorems.Thm_CategoryTheory_Abelian_Ext_injective_levelDelta_app
-- name    : CategoryTheory.Abelian.Ext.injective_levelDelta_app
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T19:15:56.905413+00:00
-- url     : https://prove2.me/theorems/53e56d78-0918-4cbb-b42b-6b87567eb154
-- title:
--   The levelwise connecting map of Ext for a short exact sequence of inverse systems is injective when the middle Ext vanishes
-- statement:
--   Let $\mathcal{A}$ be an abelian category with Ext groups and let $Z$ be an object of $\mathcal{A}$. Let $0 \to X_1 \to X_2 \to X_3 \to 0$ be a short complex of inverse systems $\mathbb{N}^{\mathrm{op}} \to \mathcal{A}$ which is short exact at every level $k$. For each $i$ and $k$ there is the connecting homomorphism of the covariant long exact Ext sequence
--   $$\delta^i_k : \operatorname{Ext}^i(Z, X_3(k)) \longrightarrow \operatorname{Ext}^{i+1}(Z, X_1(k)),$$
--   and these assemble into a morphism of inverse systems of abelian groups. Let $j \ge 0$ and let $k$ be a level such that $\operatorname{Ext}^{j+1}(Z, X_2(k)) = 0$. Then
--   $$\delta^{j+1}_k : \operatorname{Ext}^{j+1}(Z, X_3(k)) \longrightarrow \operatorname{Ext}^{j+2}(Z, X_1(k))$$
--   is injective.
--
--   This is immediate from exactness of the long exact sequence at $\operatorname{Ext}^{j+1}(Z, X_3(k))$; it is one of the bookkeeping lemmas used to compute Ext into a sequential limit of systems.
--
--   **Formalization Note** The connecting maps are the morphism of systems `levelDelta Z hSCk i : levelSystem Z SC.X₃ i ⟶ levelSystem Z SC.X₁ (i + 1)`, where `levelSystem Z F i` is the system `n ↦ Ext Z (F.obj (op n)) i`; the statement concerns its component at `k` in degree `j + 1`. The hypotheses `EnoughInjectives`, `HasProductsOfShape ℕ` and Ext for the functor category are omitted for this lemma; only `[Abelian A] [HasExt.{w} A]` are used. Vanishing is `Subsingleton`. The Lean name is `CategoryTheory.Abelian.Ext.injective_levelDelta_app`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Algebra/Homology/DerivedCategory/Ext/SequentialLimit.lean, lines 719-730 (`CategoryTheory.Abelian.Ext.injective_levelDelta_app`).

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

theorem injective_levelDelta_app
    (hSCk : ∀ k : ℕᵒᵖ, (SC.map ((evaluation ℕᵒᵖ A).obj k)).ShortExact) (j : ℕ) (k : ℕᵒᵖ)
    (h₂ : Subsingleton (Ext Z (SC.X₂.obj k) (j + 1))) :
    Function.Injective (ConcreteCategory.hom ((levelDelta Z hSCk (j + 1)).app k)) := by sorry

end Main

end Ext
end Abelian
end CategoryTheory
