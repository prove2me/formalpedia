-- Prove2me | Theorems.Thm_CategoryTheory_Abelian_Ext_subsingleton_pi
-- name    : CategoryTheory.Abelian.Ext.subsingleton_pi
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T19:15:40.483164+00:00
-- url     : https://prove2.me/theorems/788132fb-a921-53c8-8992-ed74d10726e3
-- title:
--   If products preserve epimorphisms, a product of objects with vanishing positive Ext from $Z$ has vanishing positive Ext
-- statement:
--   Let $\mathcal{C}$ be an abelian category with Ext groups and enough injectives, and let $\iota$ be an index set such that $\mathcal{C}$ has $\iota$-indexed products. Assume that $\iota$-indexed products preserve epimorphisms: whenever $\varphi_i : A_i \to B_i$ are epimorphisms for all $i \in \iota$, the induced map $\prod_i A_i \to \prod_i B_i$ is an epimorphism. Let $Z$ be an object and $(G_i)_{i \in \iota}$ a family of objects with $\operatorname{Ext}^q(Z, G_i) = 0$ for all $i$ and all $q > 0$. Then
--   $$\operatorname{Ext}^q\Bigl(Z, \prod_{i \in \iota} G_i\Bigr) = 0 \quad \text{for all } q > 0.$$
--
--   This is used for pro-étale sheaves, where products are exact (the topos is replete), so that products of acyclic sheaves are acyclic.
--
--   **Formalization Note** The index type is `ι : Type t` with `[HasProductsOfShape ι C]` and `[EnoughInjectives C]`; Ext groups live in universe `w` via `[HasExt.{w} C]`. The exactness of products is the explicit hypothesis `hepi` about `Limits.Pi.map`. Vanishing is `Subsingleton`, and the product is `∏ᶜ G`. The Lean name is `CategoryTheory.Abelian.Ext.subsingleton_pi`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Algebra/Homology/DerivedCategory/Ext/Product.lean, lines 228-287 (`CategoryTheory.Abelian.Ext.subsingleton_pi`).

import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Definitions.Def_ProEtale_Mathlib_Algebra_Homology_DerivedCategory_Ext_Product

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

universe w w' t v v' u u'

open CategoryTheory Limits Opposite

namespace CategoryTheory
namespace Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

namespace Ext

section Pi

variable {ι : Type t} [HasProductsOfShape ι C] [EnoughInjectives C]

theorem subsingleton_pi
    (hepi : ∀ (A B : ι → C) (φ : ∀ i, A i ⟶ B i), (∀ i, Epi (φ i)) → Epi (Limits.Pi.map φ))
    (Z : C) (G : ι → C) (hG : ∀ i q, 0 < q → Subsingleton (Ext Z (G i) q)) :
    ∀ q, 0 < q → Subsingleton (Ext Z (∏ᶜ G) q) := by sorry

end Pi

end Ext

end Abelian
end CategoryTheory
