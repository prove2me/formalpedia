-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyGeneralBase_mackeyMap_hasSum_norm_sq
-- name    : BookProof.ChapterMackeyGeneralBase.mackeyMap_hasSum_norm_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T20:21:48.814622+00:00
-- url     : https://prove2.me/theorems/6d8ffb88-7787-40e1-9f05-714fcadba819
-- title:
--   The Lean 4 theorem `mackeyMap_hasSum_norm_sq` in the `ChapterMackeyGeneralBase` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `mackeyMap_hasSum_norm_sq` in the `ChapterMackeyGeneralBase` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMackeyGeneralBase.lean

-- Generated from ChapterMackeyGeneralBase.lean — theorem BookProof.ChapterMackeyGeneralBase.mackeyMap_hasSum_norm_sq
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

theorem BookProof.ChapterMackeyGeneralBase.mackeyMap_hasSum_norm_sq (ψ : E) :
    HasSum (fun x => ‖mackeyMap S s ψ x‖ ^ 2) (‖ψ‖ ^ 2) := by sorry
