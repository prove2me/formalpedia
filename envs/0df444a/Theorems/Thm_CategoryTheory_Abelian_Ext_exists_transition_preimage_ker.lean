-- Prove2me | Theorems.Thm_CategoryTheory_Abelian_Ext_exists_transition_preimage_ker
-- name    : CategoryTheory.Abelian.Ext.exists_transition_preimage_ker
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T19:15:52.412809+00:00
-- url     : https://prove2.me/theorems/241203ff-27d6-5aee-86a4-793d158234c3
-- title:
--   Mittag-Leffler on Hom into the first term gives the stabilized Mittag-Leffler condition for kernels of Hom into the second-to-third map
-- statement:
--   Let $\mathcal A$ be an abelian category, $Z\in\mathcal A$, and let $0\to X_1\to X_2\xrightarrow{g} X_3\to 0$ be a short complex of inverse systems $\mathbb N^{\mathrm{op}}\to\mathcal A$ which is short exact at every level $k$. Write $g_* : \operatorname{Hom}(Z, X_2(k))\to\operatorname{Hom}(Z, X_3(k))$ for the induced maps (as $\operatorname{Ext}^0$). Assume that the inverse system of sets $n\mapsto \operatorname{Hom}(Z, X_1(n))$ satisfies the Mittag-Leffler condition. Then the kernels of $g_*$ satisfy the following stabilized Mittag-Leffler condition: for every $n$ there exists $m\ge n$ such that for every $k\ge n$ and every $b\in\operatorname{Hom}(Z,X_2(m))$ with $g_*(b)=0$, there is $b'\in\operatorname{Hom}(Z,X_2(k))$ with $g_*(b')=0$ and
--   $$b'|_{n} \;=\; b|_{n} \quad\text{in } \operatorname{Hom}(Z, X_2(n)),$$
--   where $(-)|_n$ denotes composition with the transition maps $X_2(m)\to X_2(n)$, resp. $X_2(k)\to X_2(n)$.
--
--   This is the input needed to apply the exchange of limits and cokernels for towers of abelian groups to the sequence $\operatorname{Hom}(Z,X_1)\to\operatorname{Hom}(Z,X_2)\to\operatorname{Hom}(Z,X_3)$, in the study of Ext groups into sequential limits.
--
--   **Formalization Note** Only `[Abelian A]` and `[HasExt.{w} A]` are used (the section instances on `ℕᵒᵖ ⥤ A`, enough injectives and products are omitted). The short complex is `SC : ShortComplex (ℕᵒᵖ ⥤ A)`, levelwise short exactness is `(SC.map ((evaluation ℕᵒᵖ A).obj k)).ShortExact`, and the Mittag-Leffler hypothesis is `(levelSystem Z SC.X₁ 0 ⋙ forget AddCommGrpCat).IsMittagLeffler`, where `levelSystem Z F i = F ⋙ extFunctorObj Z i`. The Hom groups are literally `Ext Z (-) 0`. Note that $k$ is only required to satisfy $k\ge n$, not $k\ge m$.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Algebra/Homology/DerivedCategory/Ext/SequentialLimit.lean, lines 748-818 (`CategoryTheory.Abelian.Ext.exists_transition_preimage_ker`).

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

theorem exists_transition_preimage_ker
    (hSCk : ∀ k : ℕᵒᵖ, (SC.map ((evaluation ℕᵒᵖ A).obj k)).ShortExact)
    (hML : (levelSystem Z SC.X₁ 0 ⋙
      CategoryTheory.forget AddCommGrpCat.{w}).IsMittagLeffler) :
    ∀ n : ℕ, ∃ (m : ℕ) (hm : n ≤ m), ∀ (k : ℕ) (hk : n ≤ k),
      ∀ b : Ext Z (SC.X₂.obj (op m)) 0,
        ConcreteCategory.hom
          ((Functor.whiskerRight SC.g (extFunctorObj Z 0)).app (op m)) b = 0 →
        ∃ b' : Ext Z (SC.X₂.obj (op k)) 0,
          ConcreteCategory.hom
            ((Functor.whiskerRight SC.g (extFunctorObj Z 0)).app (op k)) b' = 0 ∧
          ConcreteCategory.hom ((levelSystem Z SC.X₂ 0).map (homOfLE hk).op) b' =
            ConcreteCategory.hom ((levelSystem Z SC.X₂ 0).map (homOfLE hm).op) b := by sorry

end Main

end Ext
end Abelian
end CategoryTheory
