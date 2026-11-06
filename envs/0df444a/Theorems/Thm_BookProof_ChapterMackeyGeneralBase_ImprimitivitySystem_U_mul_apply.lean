-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyGeneralBase_ImprimitivitySystem_U_mul_apply
-- name    : BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem.U_mul_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T20:21:29.568817+00:00
-- url     : https://prove2.me/theorems/8cb565b7-0cd1-4e63-97ca-fd8a5f72fc83
-- title:
--   The Lean 4 theorem `U_mul_apply` in the `ChapterMackeyGeneralBase` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `U_mul_apply` in the `ChapterMackeyGeneralBase` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMackeyGeneralBase.lean

-- Generated from ChapterMackeyGeneralBase.lean — theorem BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem.U_mul_apply
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

theorem BookProof.ChapterMackeyGeneralBase.ImprimitivitySystem.U_mul_apply (g h : G) (ψ : E) : S.U g (S.U h ψ) = S.U (g * h) ψ := by sorry
