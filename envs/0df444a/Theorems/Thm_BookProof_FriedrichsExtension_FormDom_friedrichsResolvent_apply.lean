-- Prove2me | Theorems.Thm_BookProof_FriedrichsExtension_FormDom_friedrichsResolvent_apply
-- name    : BookProof.FriedrichsExtension.FormDom.friedrichsResolvent_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-03T14:08:08.028454+00:00
-- url     : https://prove2.me/theorems/5abea042-abab-4f6b-a753-c444ed5efcbf
-- title:
--   The Lean 4 theorem `friedrichsResolvent_apply` in the `ChapterFriedrichsExtension` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.FriedrichsExtension.FormDom.friedrichsResolvent_apply` from the timepiece Lean 4 formalization (source chapter `BookProof/ChapterFriedrichsExtension.lean`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFriedrichsExtension.lean

-- Generated from ChapterFriedrichsExtension.lean — theorem BookProof.FriedrichsExtension.FormDom.friedrichsResolvent_apply
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib
import Definitions.Def_ChapterFriedrichsExtension
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable [CompleteSpace F]



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.HermiteGalerkin
open scoped InnerProductSpace ENNReal lp

theorem BookProof.FriedrichsExtension.FormDom.friedrichsResolvent_apply (P : PosSymOp F) (u v : F) :
    (inner ℂ u (friedrichsResolvent P v) : ℂ) = inner ℂ (formRiesz P u) (formRiesz P v) := by sorry
