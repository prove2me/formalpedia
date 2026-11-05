-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyGeneralBase_ImprimitivitySystem_U_inv_apply
-- name    : BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem.U_inv_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-04T20:21:17.202199+00:00
-- url     : https://prove2.me/theorems/a238f0a9-b951-4742-a037-dbf2f99ad640
-- title:
--   The Lean 4 theorem `U_inv_apply` in the `ChapterMackeyGeneralBase` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `U_inv_apply` in the `ChapterMackeyGeneralBase` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMackeyGeneralBase.lean

-- Generated from ChapterMackeyGeneralBase.lean — theorem BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem.U_inv_apply
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

theorem BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem.U_inv_apply (g : G) (ψ : E) : S.U g⁻¹ (S.U g ψ) = ψ := by sorry
