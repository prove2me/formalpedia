-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyGeneralBase_mackeyMap_smul
-- name    : BookProof.ChapterMackeyGeneralBase.mackeyMap_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T20:21:47.927939+00:00
-- url     : https://prove2.me/theorems/b1a105db-0544-4ac4-8a80-8c158ee99943
-- title:
--   The Lean 4 theorem `mackeyMap_smul` in the `ChapterMackeyGeneralBase` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `mackeyMap_smul` in the `ChapterMackeyGeneralBase` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMackeyGeneralBase.lean

-- Generated from ChapterMackeyGeneralBase.lean — theorem BookProof.ChapterMackeyGeneralBase.mackeyMap_smul
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

theorem BookProof.ChapterMackeyGeneralBase.mackeyMap_smul (a : ℂ) (ψ : E) : mackeyMap S s (a • ψ) = a • mackeyMap S s ψ := by sorry
