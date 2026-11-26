-- Prove2me | Theorems.Thm_CategoryTheory_Abelian_Ext_surjective_limMap_and_exact
-- name    : CategoryTheory.Abelian.Ext.surjective_limMap_and_exact
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T19:16:40.891711+00:00
-- url     : https://prove2.me/theorems/84db0651-a706-4447-b62b-1431464b291f
-- title:
--   Exchange of inverse limits and cokernels for towers of abelian groups under a Mittag-Leffler condition on kernels
-- statement:
--   Let $B\xrightarrow{g} C\xrightarrow{h} D$ be morphisms of inverse systems of abelian groups indexed by $\mathbb N$ (functors $\mathbb N^{\mathrm{op}}\to\mathbf{Ab}$). Assume:
--
--   1. $h_k\circ g_k = 0$ for every $k$;
--   2. levelwise exactness at $C$: every $c\in C_k$ with $h_k(c)=0$ is of the form $g_k(b)$ for some $b\in B_k$;
--   3. every $h_k$ is surjective;
--   4. every transition map $B_{n+1}\to B_n$ is surjective;
--   5. the kernels of $g$ satisfy the stabilized Mittag-Leffler condition: for every $n$ there is $m\ge n$ such that for all $k\ge n$ and all $b\in B_m$ with $g_m(b)=0$ there is $b'\in B_k$ with $g_k(b')=0$ and $b'|_n = b|_n$ in $B_n$ (restriction along the transition maps).
--
--   Then the induced maps on limits $\lim g : \lim B\to\lim C$ and $\lim h:\lim C\to\lim D$ satisfy
--   $$\lim h \text{ is surjective}, \qquad \ker(\lim h) \subseteq \operatorname{im}(\lim g).$$
--   In other words, $\lim h$ induces a surjection from the cokernel of $\lim g$ onto $\lim D$ whose kernel is trivial, so $\operatorname{coker}(\lim g)\cong \lim D$.
--
--   This is the diagram chase behind the comparison of Ext groups into a sequential limit with the limit of Ext groups, where it is applied to Hom/Ext groups of a levelwise short exact sequence of inverse systems.
--
--   **Formalization Note** `B C D : ℕᵒᵖ ⥤ AddCommGrpCat.{w}`, `g : B ⟶ C`, `h : C ⟶ D`; all hypotheses are elementwise, via `ConcreteCategory.hom`. Transition maps are `SequentialSystem.transition B n`, and $b|_n$ is `B.map (homOfLE _).op`. The conclusion is a conjunction: `Function.Surjective (limMap h)` and every `c` in `limit C` with `limMap h c = 0` is `limMap g b` for some `b` in `limit B`. The phrase "induces an isomorphism from the cokernel" is a paraphrase of this conjunction together with hypothesis 1, not part of the Lean statement.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Algebra/Homology/DerivedCategory/Ext/SequentialLimit.lean, lines 406-620 (`CategoryTheory.Abelian.Ext.surjective_limMap_and_exact`).

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

theorem surjective_limMap_and_exact
    (hcomp : ∀ (k : ℕᵒᵖ) (b : B.obj k), ConcreteCategory.hom (h.app k)
      (ConcreteCategory.hom (g.app k) b) = 0)
    (hexact : ∀ (k : ℕᵒᵖ) (c : C.obj k), ConcreteCategory.hom (h.app k) c = 0 →
      ∃ b : B.obj k, ConcreteCategory.hom (g.app k) b = c)
    (hsurj : ∀ k, Function.Surjective (ConcreteCategory.hom (h.app k)))
    (hB : ∀ n, Function.Surjective
      (ConcreteCategory.hom (SequentialSystem.transition B n)))
    (hker : ∀ n : ℕ, ∃ (m : ℕ) (hm : n ≤ m), ∀ (k : ℕ) (hk : n ≤ k),
      ∀ b : B.obj (op m), ConcreteCategory.hom (g.app (op m)) b = 0 →
        ∃ b' : B.obj (op k), ConcreteCategory.hom (g.app (op k)) b' = 0 ∧
          ConcreteCategory.hom (B.map (homOfLE hk).op) b' =
            ConcreteCategory.hom (B.map (homOfLE hm).op) b) :
    Function.Surjective (ConcreteCategory.hom (limMap h)) ∧
      ∀ c : (limit C : AddCommGrpCat.{w}), ConcreteCategory.hom (limMap h) c = 0 →
        ∃ b : (limit B : AddCommGrpCat.{w}), ConcreteCategory.hom (limMap g) b = c := by sorry

end AbChase

end Ext
end Abelian
end CategoryTheory
