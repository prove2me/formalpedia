-- Prove2me | Theorems.Thm_CategoryTheory_SequentialSystem_epi_transition_of_epi_app
-- name    : CategoryTheory.SequentialSystem.epi_transition_of_epi_app
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T19:16:38.89106+00:00
-- url     : https://prove2.me/theorems/a74e6bda-cc27-4986-a2d3-d0bf1004be94
-- title:
--   A levelwise epimorphic quotient of an inverse system with epimorphic transitions has epimorphic transitions
-- statement:
--   Let $\mathcal{C}$ be a category and let $F, G : \mathbb{N}^{\mathrm{op}} \to \mathcal{C}$ be inverse systems. Let $\tau : F \to G$ be a morphism of systems such that every component $\tau_k : F(k) \to G(k)$ is an epimorphism, and suppose all transition maps $F(n+1) \to F(n)$ of $F$ are epimorphisms. Then for every $n$ the transition map
--   $$G(n+1) \longrightarrow G(n)$$
--   is an epimorphism.
--
--   This follows from the naturality square $G(n+1 \to n) \circ \tau_{n+1} = \tau_n \circ F(n+1 \to n)$, whose right-hand side is an epimorphism. It is used, for example, to see that various systems of sheaves built as quotients have surjective transitions.
--
--   **Formalization Note** No assumption on $\mathcal{C}$ is needed. The transition map is `SequentialSystem.transition G n : G.obj (op (n + 1)) ⟶ G.obj (op n)`. The Lean name is `CategoryTheory.SequentialSystem.epi_transition_of_epi_app`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/Abelian/SequentialSystem.lean, lines 72-85 (`CategoryTheory.SequentialSystem.epi_transition_of_epi_app`).

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

theorem epi_transition_of_epi_app {F G : ℕᵒᵖ ⥤ C} (τ : F ⟶ G)
    (hτ : ∀ k, Epi (τ.app k)) (hF : ∀ n, Epi (transition F n)) (n : ℕ) :
    Epi (transition G n) := by sorry

end Transition

end SequentialSystem
end CategoryTheory
