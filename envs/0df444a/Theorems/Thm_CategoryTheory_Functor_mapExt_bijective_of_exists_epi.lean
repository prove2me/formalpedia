-- Prove2me | Theorems.Thm_CategoryTheory_Functor_mapExt_bijective_of_exists_epi
-- name    : CategoryTheory.Functor.mapExt_bijective_of_exists_epi
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T19:15:45.204477+00:00
-- url     : https://prove2.me/theorems/68e3629d-e121-513f-9dd9-79fbda029534
-- title:
--   An exact fully faithful functor induces isomorphisms on all Ext groups if objects are covered by relatively acyclic objects
-- statement:
--   Let $\mathcal C$ and $\mathcal D$ be abelian categories with Ext groups, and suppose $\mathcal C$ has enough injectives. Let $F:\mathcal C\to\mathcal D$ be an additive functor that is exact (preserves finite limits and finite colimits) and fully faithful. Assume that for every object $X\in\mathcal C$ there exist an object $P$ and an epimorphism $\pi : P\twoheadrightarrow X$ such that
--   $$\operatorname{Ext}^{n+1}_{\mathcal D}\big(F(P), F(I)\big) = 0 \qquad\text{for every injective } I\in\mathcal C \text{ and every } n\ge 0.$$
--   Then for all objects $X, Y\in\mathcal C$ and every $n\in\mathbb N$, the map induced by $F$
--   $$\operatorname{Ext}^n_{\mathcal C}(X,Y) \longrightarrow \operatorname{Ext}^n_{\mathcal D}\big(F(X),F(Y)\big)$$
--   is bijective.
--
--   This is a criterion for an exact embedding of abelian categories to preserve Ext groups, where the acyclicity of images of injectives only needs to be tested against a class of objects that covers every object by an epimorphism. In the pro-étale project it is used to compare cohomology computed in different categories of sheaves.
--
--   **Formalization Note** Universes: `C : Type u` with `Category.{v}`, `D : Type u'` with `Category.{v'}`, and Ext groups in `HasExt.{w} C`, `HasExt.{w'} D`. The map is Mathlib's `F.mapExtAddHom X Y n`. Vanishing is `Subsingleton`. The fork describes this as a variant of `Functor.mapExt_bijective_of_subsingleton_ext_injective`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Algebra/Homology/DerivedCategory/Ext/MapBijective.lean, lines 65-105 (`CategoryTheory.Functor.mapExt_bijective_of_exists_epi`).

import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

universe w w' v v' u u'

namespace CategoryTheory

open Limits Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

attribute [local simp] Ext.mapExactFunctor_comp Ext.mapExactFunctor_mk₀
  Ext.mapExactFunctor_extClass

theorem Functor.mapExt_bijective_of_exists_epi
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Full] [F.Faithful] [HasExt.{w} C] [HasExt.{w'} D] [EnoughInjectives C]
    (hP : ∀ X : C, ∃ (P : C) (π : P ⟶ X), Epi π ∧ ∀ (I : C), Injective I → ∀ (n : ℕ),
      Subsingleton (Ext (F.obj P) (F.obj I) (n + 1)))
    (X Y : C) (n : ℕ) : Function.Bijective (F.mapExtAddHom X Y n) := by sorry

end CategoryTheory
