-- Prove2me | Theorems.Thm_CategoryTheory_Abelian_Ext_isMittagLeffler_of_exact
-- name    : CategoryTheory.Abelian.Ext.isMittagLeffler_of_exact
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T19:16:21.08647+00:00
-- url     : https://prove2.me/theorems/ada02ebc-1e6e-4de7-b3e8-c378b401535b
-- title:
--   Mittag-Leffler passes to the middle of a levelwise exact sequence of towers with surjective left transitions
-- statement:
--   Let $B, C, D$ be inverse systems of abelian groups indexed by $\mathbb{N}$ (functors $\mathbb{N}^{\mathrm{op}} \to \mathbf{Ab}$), with morphisms of systems $g : B \to C$ and $h : C \to D$. Assume that
--   1. at every level $k$, every $c \in C_k$ with $h_k(c) = 0$ is of the form $g_k(b)$ for some $b \in B_k$;
--   2. each $h_k : C_k \to D_k$ is surjective;
--   3. the transition maps $B_{n+1} \to B_n$ are surjective for every $n$;
--   4. $D$, viewed as an inverse system of sets, satisfies the Mittag-Leffler condition.
--
--   Then $C$, viewed as an inverse system of sets, satisfies the Mittag-Leffler condition: for every $n$ there is $m \ge n$ such that for all $k \ge n$ the image of $C_m \to C_n$ is contained in the image of $C_k \to C_n$.
--
--   This is used when passing Ext groups through sequential limits, where one needs $\varprojlim^1$ of certain towers of Ext groups to vanish.
--
--   **Formalization Note** The groups lie in `AddCommGrpCat.{w}`. Hypothesis 1 is only the inclusion $\ker h_k \subseteq \operatorname{im} g_k$; no assumption $h \circ g = 0$ is made. Mittag-Leffler is Mathlib's `Functor.IsMittagLeffler` for the composite with the forgetful functor to types, and the transition maps are `SequentialSystem.transition B n`. The Lean name is `CategoryTheory.Abelian.Ext.isMittagLeffler_of_exact`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Algebra/Homology/DerivedCategory/Ext/SequentialLimit.lean, lines 342-404 (`CategoryTheory.Abelian.Ext.isMittagLeffler_of_exact`).

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

theorem isMittagLeffler_of_exact
    (hexact : ∀ (k : ℕᵒᵖ) (c : C.obj k), ConcreteCategory.hom (h.app k) c = 0 →
      ∃ b : B.obj k, ConcreteCategory.hom (g.app k) b = c)
    (hsurj : ∀ k, Function.Surjective (ConcreteCategory.hom (h.app k)))
    (hB : ∀ n, Function.Surjective
      (ConcreteCategory.hom (SequentialSystem.transition B n)))
    (hD : (D ⋙ CategoryTheory.forget AddCommGrpCat.{w}).IsMittagLeffler) :
    (C ⋙ CategoryTheory.forget AddCommGrpCat.{w}).IsMittagLeffler := by sorry

end AbChase

end Ext
end Abelian
end CategoryTheory
