-- Prove2me | Theorems.Thm_CategoryTheory_SequentialSystem_epi_map_of_epi_transition
-- name    : CategoryTheory.SequentialSystem.epi_map_of_epi_transition
-- status  : Proved
-- author  : @Idealson
-- created : 2026-11-26T19:16:43.804097+00:00
-- url     : https://prove2.me/theorems/574ad004-fede-439d-9324-c272b84990ad
-- title:
--   If the successive transition maps of an inverse sequence are epimorphisms, so are all its transition maps
-- statement:
--   Let $\mathcal C$ be a category and $(F_n)_{n\in\mathbb N}$ an inverse system in $\mathcal C$ (a functor $\mathbb N^{\mathrm{op}}\to\mathcal C$). Suppose every successive transition map $F_{n+1}\to F_n$ is an epimorphism. Then for all $m\le n$, the transition map
--   $$F_n \longrightarrow F_m$$
--   is an epimorphism.
--
--   This follows the usual pattern that properties stable under composition propagate from successive transition maps to all transition maps; it is used for towers such as $(\mathbb Z/\ell^n)_n$.
--
--   **Formalization Note** No assumptions on the category beyond `Category`. The successive transition maps are `transition F n : F.obj (op (n + 1)) ⟶ F.obj (op n)` and the general one is `F.map (homOfLE hmn).op`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/Abelian/SequentialSystem.lean, lines 50-70 (`CategoryTheory.SequentialSystem.epi_map_of_epi_transition`).

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

theorem epi_map_of_epi_transition (F : ℕᵒᵖ ⥤ C)
    (hF : ∀ n, Epi (transition F n)) {m n : ℕ} (hmn : m ≤ n) :
    Epi (F.map (homOfLE hmn).op) := by sorry

end Transition

end SequentialSystem
end CategoryTheory
