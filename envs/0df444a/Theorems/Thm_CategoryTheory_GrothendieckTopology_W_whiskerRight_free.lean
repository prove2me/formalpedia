-- Prove2me | Theorems.Thm_CategoryTheory_GrothendieckTopology_W_whiskerRight_free
-- name    : CategoryTheory.GrothendieckTopology.W.whiskerRight_free
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T19:16:08.993144+00:00
-- url     : https://prove2.me/theorems/6476a4a5-ef5f-4665-86b9-ed9c19adf81a
-- title:
--   Applying the free abelian group functor preserves morphisms of presheaves that become isomorphisms after sheafification
-- statement:
--   Let $\mathcal{C}$ be a category with a Grothendieck topology $J$, and let $\varphi : P \to Q$ be a morphism of presheaves of sets on $\mathcal{C}$ which lies in the class $W_J$ of morphisms inverted by sheafification (equivalently, inducing an isomorphism of associated sheaves). Then the induced morphism of presheaves of abelian groups
--   $$\mathbb{Z}[\varphi] : \mathbb{Z}[P] \longrightarrow \mathbb{Z}[Q],$$
--   obtained by applying the free abelian group functor objectwise, also lies in $W_J$, i.e. becomes an isomorphism after sheafification.
--
--   This is used in the construction of the Čech resolution of free abelian sheaves, to transfer local bijectivity statements about presheaves of sets to the free abelian presheaves on them.
--
--   **Formalization Note** The category is `C : Type (u + 1)` with morphisms in `Type u`; presheaves of sets take values in `Type (u + 1)` and the free functor is `AddCommGrpCat.free.{u + 1}`, applied by `Functor.whiskerRight`. The class `J.W` is Mathlib's `GrothendieckTopology.W`, used here for both types and abelian groups as coefficient categories. The ambient assumptions `HasFiniteWidePullbacks C` and `HasWeakSheafify J AddCommGrpCat` are omitted for this lemma. The Lean name is `CategoryTheory.GrothendieckTopology.W.whiskerRight_free`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/Sites/SheafCohomology/CechResolution.lean, lines 517-534 (`CategoryTheory.GrothendieckTopology.W.whiskerRight_free`).

import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_SheafCohomology_FreeAbelianSheaf
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Sites_SheafCohomology_CechResolution

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits Opposite AlgebraicTopology
open scoped Simplicial

namespace CategoryTheory

variable {C : Type (u + 1)} [Category.{u} C] [HasFiniteWidePullbacks C]
variable (J : GrothendieckTopology C) [HasWeakSheafify J AddCommGrpCat.{u + 1}]

variable {U V : C} (f : V ⟶ U) {W : C}

section Resolution

variable {f}

variable (f)

omit [HasFiniteWidePullbacks C] [HasWeakSheafify J AddCommGrpCat.{u + 1}] in

theorem GrothendieckTopology.W.whiskerRight_free {P Q : Cᵒᵖ ⥤ Type (u + 1)} {φ : P ⟶ Q}
    (hφ : J.W φ) : J.W (Functor.whiskerRight φ AddCommGrpCat.free.{u + 1}) := by sorry

end Resolution

end CategoryTheory
