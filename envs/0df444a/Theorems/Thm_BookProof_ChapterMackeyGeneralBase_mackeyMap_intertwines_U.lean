-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyGeneralBase_mackeyMap_intertwines_U
-- name    : BookProof.ChapterMackeyGeneralBase.mackeyMap_intertwines_U
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-04T20:21:50.111869+00:00
-- url     : https://prove2.me/theorems/222dd524-5a8b-41f4-9fb6-64c6cf7ec7d3
-- title:
--   The Lean 4 theorem `mackeyMap_intertwines_U` in the `ChapterMackeyGeneralBase` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `mackeyMap_intertwines_U` in the `ChapterMackeyGeneralBase` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMackeyGeneralBase.lean

-- Generated from ChapterMackeyGeneralBase.lean — theorem BookProof.ChapterMackeyGeneralBase.mackeyMap_intertwines_U
import Definitions.Def_ChapterOrthogonalSums
import Mathlib
import Definitions.Def_ChapterMackeyGeneralBase
import Definitions.Def_ChapterMackeyImprimitivity
import Definitions.Def_ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity


open scoped InnerProductSpace


open BookProof.ChapterOrthogonalSums

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable (S : BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem G X E)
variable (S : BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem G X E) (x₀ : X) (s : X → G)
variable {S x₀ s}

theorem BookProof.ChapterMackeyGeneralBase.mackeyMap_intertwines_U (hs : ∀ x, s x • x₀ = x) (g : G) (ψ : E) :
    mackeyMap S s (S.U g ψ) = inducedRep S s g (mackeyMap S s ψ) := by sorry
