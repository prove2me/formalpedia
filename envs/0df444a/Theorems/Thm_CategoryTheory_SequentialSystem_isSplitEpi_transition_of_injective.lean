-- Prove2me | Theorems.Thm_CategoryTheory_SequentialSystem_isSplitEpi_transition_of_injective
-- name    : CategoryTheory.SequentialSystem.isSplitEpi_transition_of_injective
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T19:16:45.185272+00:00
-- url     : https://prove2.me/theorems/a9917155-477f-4ecd-b540-5ace875b9bc5
-- title:
--   The transition maps of an injective inverse system are split epimorphisms
-- statement:
--   Let $\mathcal{C}$ be a category with zero morphisms and a zero object, and let $I : \mathbb{N}^{\mathrm{op}} \to \mathcal{C}$ be an inverse system which is an injective object of the functor category $\mathrm{Fun}(\mathbb{N}^{\mathrm{op}}, \mathcal{C})$. Then for every $n$ the transition map
--   $$I(n+1) \longrightarrow I(n)$$
--   is a split epimorphism.
--
--   In particular injective inverse systems have surjective transition maps, hence vanishing $\varprojlim^1$; this is the starting point for computing the derived functors of $\varprojlim$ on sequential systems.
--
--   **Formalization Note** The hypotheses are `[HasZeroMorphisms C] [HasZeroObject C]` and `[Injective I]` in `ℕᵒᵖ ⥤ C`. The conclusion is the typeclass `IsSplitEpi (transition I n)`, i.e. existence of a section. The Lean name is `CategoryTheory.SequentialSystem.isSplitEpi_transition_of_injective`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/Abelian/SequentialSystem.lean, lines 477-484 (`CategoryTheory.SequentialSystem.isSplitEpi_transition_of_injective`).

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

theorem isSplitEpi_transition_of_injective (I : ℕᵒᵖ ⥤ C) [Injective I] (n : ℕ) :
    IsSplitEpi (transition I n) := by sorry

end Injective

end SequentialSystem
end CategoryTheory
