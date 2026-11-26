-- Prove2me | Theorems.Thm_CategoryTheory_Sheaf_exists_mem_ext_map_eq_zero
-- name    : CategoryTheory.Sheaf.exists_mem_ext_map_eq_zero
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T19:16:30.258348+00:00
-- url     : https://prove2.me/theorems/4cd59a7a-4eda-4ba3-8a94-fbec27598c15
-- title:
--   Positive-degree Ext classes out of a free abelian sheaf vanish locally
-- statement:
--   Let $\mathcal{C}$ be a site with Grothendieck topology $J$ (with the size conventions below), such that sheafification of presheaves of abelian groups exists and the category of abelian sheaves has Ext groups and enough injectives. For an object $U$ let $\mathbb{Z}[U]$ be the free abelian sheaf on $U$ (the sheafification of the free abelian presheaf on the presheaf represented by $U$). Let $\mathcal{F}$ be a sheaf of abelian groups, $p \in \mathbb{N}$ and
--   $$\xi \in \operatorname{Ext}^{p+1}(\mathbb{Z}[U], \mathcal{F}).$$
--   Then there is a covering sieve $R \in J(U)$ such that for every $g : W \to U$ in $R$,
--   $$g^*\xi = \xi \circ \mathbb{Z}[g] = 0 \in \operatorname{Ext}^{p+1}(\mathbb{Z}[W], \mathcal{F}).$$
--
--   In other words, every class in $H^{p+1}(U, \mathcal{F})$ with $p+1 > 0$ becomes zero locally on $U$. This is the basic local vanishing property of sheaf cohomology, used in dimension-shifting and Čech arguments on the pro-étale site.
--
--   **Formalization Note** The site is `C : Type (u+1)` with `[Category.{u} C]`, sheaves take values in `AddCommGrpCat.{u+1}`, and Ext groups are in universe `w` via `HasExt.{w}`. The hypotheses `HasSheafify J AddCommGrpCat`, `J.HasSheafCompose (forget AddCommGrpCat)`, `J.WEqualsLocallyBijective AddCommGrpCat` and `EnoughInjectives` are typeclass assumptions. The free sheaf is `freeAbelianSheafFunctor J`, and $g^*\xi$ is `(Ext.mk₀ ((freeAbelianSheafFunctor J).map g)).comp ξ _`. The theorem is `CategoryTheory.Sheaf.exists_mem_ext_map_eq_zero`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/Sites/SheafCohomology/LocallyVanish.lean, lines 88-130 (`CategoryTheory.Sheaf.exists_mem_ext_map_eq_zero`).

import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_SheafCohomology_FreeAbelianSheaf
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_SheafCohomology_LocallyVanish

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

universe w u

open CategoryTheory Limits Opposite

namespace CategoryTheory

open Abelian

variable {C : Type (u + 1)} [Category.{u} C]
variable {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u + 1}]

variable [J.HasSheafCompose (forget AddCommGrpCat.{u + 1})]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{u + 1})]
variable [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]

theorem Sheaf.exists_mem_ext_map_eq_zero (F : Sheaf J AddCommGrpCat.{u + 1}) (p : ℕ) {U : C}
    (ξ : Ext ((freeAbelianSheafFunctor J).obj U) F (p + 1)) :
    ∃ R ∈ J U, ∀ ⦃W : C⦄ (g : W ⟶ U), R.arrows g →
      (Ext.mk₀ ((freeAbelianSheafFunctor J).map g)).comp ξ (zero_add (p + 1)) = 0 := by sorry

end CategoryTheory
