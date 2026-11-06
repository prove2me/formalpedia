-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyGeneralBase_mackeyMap_reconstruct
-- name    : BookProof.ChapterMackeyGeneralBase.mackeyMap_reconstruct
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T20:21:27.372187+00:00
-- url     : https://prove2.me/theorems/6fbc7945-caa4-4a14-8b58-a9ba9747db55
-- title:
--   The Lean 4 theorem `mackeyMap_reconstruct` in the `ChapterMackeyGeneralBase` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `mackeyMap_reconstruct` in the `ChapterMackeyGeneralBase` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMackeyGeneralBase.lean

-- Generated from ChapterMackeyGeneralBase.lean — theorem BookProof.ChapterMackeyGeneralBase.mackeyMap_reconstruct
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

theorem BookProof.ChapterMackeyGeneralBase.mackeyMap_reconstruct (ψ : E) :
    HasSum (fun x => S.U (s x) (mackeyMap S s ψ x)) ψ := by sorry
