-- Prove2me | Theorems.Thm_CategoryTheory_SequentialSystem_injective_obj_of_injective
-- name    : CategoryTheory.SequentialSystem.injective_obj_of_injective
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T19:16:55.819067+00:00
-- url     : https://prove2.me/theorems/12252cc9-13aa-4c87-9a42-93ac2a8d2d5f
-- title:
--   Each term of an injective inverse sequence is an injective object
-- statement:
--   Let $\mathcal C$ be a category with zero morphisms and a zero object, and let $I:\mathbb N^{\mathrm{op}}\to\mathcal C$ be an inverse system which is an injective object of the functor category $\operatorname{Fun}(\mathbb N^{\mathrm{op}},\mathcal C)$. Then for every $n\in\mathbb N$ the object $I_n = I(n)$ is injective in $\mathcal C$.
--
--   This is used when computing Ext groups in the category of inverse systems (for instance for continuous étale cohomology) via injective resolutions, to know that evaluation at each level sends injectives to injectives.
--
--   **Formalization Note** Assumptions are `[HasZeroMorphisms C] [HasZeroObject C]` and `[Injective I]` for `I : ℕᵒᵖ ⥤ C`; the conclusion is `Injective (I.obj (op n))`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/Abelian/SequentialSystem.lean, lines 486-495 (`CategoryTheory.SequentialSystem.injective_obj_of_injective`).

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Abelian_SequentialSystem
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Abelian_SequentialSystem_Lib

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false

universe w v v' u u'

open CategoryTheory Limits Opposite

open scoped ZeroObject

namespace CategoryTheory
namespace SequentialSystem

variable {C : Type u} [Category.{v} C]

section Injective

variable [HasZeroMorphisms C] [HasZeroObject C]

theorem injective_obj_of_injective (I : ℕᵒᵖ ⥤ C) [Injective I] (n : ℕ) :
    Injective (I.obj (op n)) := by sorry

end Injective

end SequentialSystem
end CategoryTheory
