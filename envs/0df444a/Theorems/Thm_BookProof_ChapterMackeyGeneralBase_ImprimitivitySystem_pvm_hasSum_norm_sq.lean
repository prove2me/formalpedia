-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyGeneralBase_ImprimitivitySystem_pvm_hasSum_norm_sq
-- name    : BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem.pvm_hasSum_norm_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T20:21:41.4324+00:00
-- url     : https://prove2.me/theorems/058db00e-0952-45f2-b19a-9dc57c4ae26c
-- title:
--   The Lean 4 theorem `pvm_hasSum_norm_sq` in the `ChapterMackeyGeneralBase` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `pvm_hasSum_norm_sq` in the `ChapterMackeyGeneralBase` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMackeyGeneralBase.lean

-- Generated from ChapterMackeyGeneralBase.lean — theorem BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem.pvm_hasSum_norm_sq
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

theorem BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem.pvm_hasSum_norm_sq (ψ : E) : HasSum (fun x => ‖S.p x ψ‖ ^ 2) (‖ψ‖ ^ 2) := by sorry
