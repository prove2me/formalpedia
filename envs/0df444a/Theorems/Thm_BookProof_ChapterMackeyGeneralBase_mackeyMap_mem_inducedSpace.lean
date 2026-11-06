-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyGeneralBase_mackeyMap_mem_inducedSpace
-- name    : BookProof.ChapterMackeyGeneralBase.mackeyMap_mem_inducedSpace
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T20:21:56.494553+00:00
-- url     : https://prove2.me/theorems/154bfdb8-7083-47a3-8311-ae1622b54fd7
-- title:
--   The Lean 4 theorem `mackeyMap_mem_inducedSpace` in the `ChapterMackeyGeneralBase` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `mackeyMap_mem_inducedSpace` in the `ChapterMackeyGeneralBase` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMackeyGeneralBase.lean

-- Generated from ChapterMackeyGeneralBase.lean — theorem BookProof.ChapterMackeyGeneralBase.mackeyMap_mem_inducedSpace
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

theorem BookProof.ChapterMackeyGeneralBase.mackeyMap_mem_inducedSpace (hs : ∀ x, s x • x₀ = x) (ψ : E) :
    mackeyMap S s ψ ∈ InducedSpace S x₀ := by sorry
