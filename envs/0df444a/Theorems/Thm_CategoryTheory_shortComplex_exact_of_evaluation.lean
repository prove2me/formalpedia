-- Prove2me | Theorems.Thm_CategoryTheory_shortComplex_exact_of_evaluation
-- name    : CategoryTheory.shortComplex_exact_of_evaluation
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T19:21:00.679654+00:00
-- url     : https://prove2.me/theorems/8ec6621d-0a76-415f-bec1-dffbc8dd8fdc
-- title:
--   A short complex of presheaves of abelian groups is exact if it is exact at every object
-- statement:
--   Let $\mathcal{C}$ be a category and let
--   $$\mathcal{F}_1 \to \mathcal{F}_2 \to \mathcal{F}_3$$
--   be a short complex of presheaves of abelian groups on $\mathcal{C}$ (functors $\mathcal{C}^{\mathrm{op}} \to \mathbf{Ab}$). If for every object $X$ the short complex of abelian groups
--   $$\mathcal{F}_1(X) \to \mathcal{F}_2(X) \to \mathcal{F}_3(X)$$
--   is exact, then the short complex of presheaves is exact.
--
--   Exactness in a functor category into an abelian category is checked objectwise; this lemma is used to prove exactness of Čech complexes of free presheaves before sheafifying.
--
--   **Formalization Note** The category is `C : Type (u+1)` with `[Category.{u} C]`, and the presheaves take values in `AddCommGrpCat.{u+1}`; the section assumption `HasFiniteWidePullbacks C` is omitted (the declared variables `J` and `HasWeakSheafify` are not used by the statement). Evaluation at $X$ is `(evaluation Cᵒᵖ AddCommGrpCat).obj X` and exactness is `ShortComplex.Exact`. The theorem is `CategoryTheory.shortComplex_exact_of_evaluation`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/Sites/SheafCohomology/CechResolution.lean, lines 505-515 (`CategoryTheory.shortComplex_exact_of_evaluation`).

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

omit [HasFiniteWidePullbacks C] in

theorem shortComplex_exact_of_evaluation (S : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}))
    (hS : ∀ X : Cᵒᵖ, (S.map ((evaluation Cᵒᵖ AddCommGrpCat.{u + 1}).obj X)).Exact) :
    S.Exact := by sorry

end Resolution

end CategoryTheory
