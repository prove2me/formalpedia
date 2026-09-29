-- Prove2me | Theorems.Thm_BookProof_FriedrichsExtension_FormDom_incl_apply
-- name    : BookProof.FriedrichsExtension.FormDom.incl_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:25:05.585395+00:00
-- url     : https://prove2.me/theorems/40266d49-860f-42ff-a01e-19f82e9cdc4e
-- title:
--   The Lean 4 theorem `incl_apply` in the `ChapterFriedrichsExtension` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `incl_apply` in the `ChapterFriedrichsExtension` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFriedrichsExtension.lean

-- Generated from ChapterFriedrichsExtension.lean — theorem BookProof.FriedrichsExtension.FormDom.incl_apply
import Mathlib
import Definitions.Def_ChapterFriedrichsExtension
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.HermiteGalerkin

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.FriedrichsExtension.FormDom.incl_apply {P : PosSymOp F} (x : FormDom P) : incl P x = toAmbient x := by sorry
