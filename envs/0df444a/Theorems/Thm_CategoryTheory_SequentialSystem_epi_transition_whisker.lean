-- Prove2me | Theorems.Thm_CategoryTheory_SequentialSystem_epi_transition_whisker
-- name    : CategoryTheory.SequentialSystem.epi_transition_whisker
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T17:03:49.804106+00:00
-- url     : https://prove2.me/theorems/35c14a8c-8929-4cdc-861b-b291560a0396
-- title:
--   A functor preserving epimorphisms preserves inverse sequences with epimorphic transition maps
-- statement:
--   Let $\mathcal{C}$ and $\mathcal{D}$ be categories, let $F : \mathbb{N}^{\mathrm{op}} \to \mathcal{C}$ be an inverse sequence whose transition maps $F_{n+1} \to F_n$ are all epimorphisms, and let $L : \mathcal{C} \to \mathcal{D}$ be a functor that preserves epimorphisms. Then for every $n \in \mathbb{N}$ the transition map
--   $$L(F_{n+1}) \longrightarrow L(F_n)$$
--   of the inverse sequence $L \circ F$ is an epimorphism.
--
--   This is a routine bookkeeping lemma, used for instance to pass from an inverse system of étale sheaves with epimorphic transitions to its pullback to the pro-étale site.
--
--   **Formalization Note** Arbitrary universes: `C : Type u` with `Category.{v}` and `D : Type u'` with `Category.{v'}`. The transition map is `SequentialSystem.transition F n`, i.e. `F.map` of the morphism $n \le n+1$, and $L \circ F$ is written `F ⋙ L`. The theorem is `CategoryTheory.SequentialSystem.epi_transition_whisker`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/Abelian/SequentialSystem.lean, lines 87-91 (`CategoryTheory.SequentialSystem.epi_transition_whisker`).

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

section Transition

theorem epi_transition_whisker {D : Type u'} [Category.{v'} D] {F : ℕᵒᵖ ⥤ C} (L : C ⥤ D)
    [L.PreservesEpimorphisms] (hF : ∀ n, Epi (transition F n)) (n : ℕ) :
    Epi (transition (F ⋙ L) n) := by sorry

end Transition

end SequentialSystem
end CategoryTheory
