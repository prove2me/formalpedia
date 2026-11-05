-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyGeneralBase_ImprimitivitySystem_U_apply_inv
-- name    : BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem.U_apply_inv
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-04T20:21:15.30434+00:00
-- url     : https://prove2.me/theorems/49f79ddd-ed92-40f5-9b2f-31582faeb72b
-- title:
--   The Lean 4 theorem `U_apply_inv` in the `ChapterMackeyGeneralBase` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `U_apply_inv` in the `ChapterMackeyGeneralBase` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMackeyGeneralBase.lean

-- Generated from ChapterMackeyGeneralBase.lean — theorem BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem.U_apply_inv
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

theorem BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem.U_apply_inv (g : G) (ψ : E) : S.U g (S.U g⁻¹ ψ) = ψ := by sorry
