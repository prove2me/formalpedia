-- Prove2me | Theorems.Thm_BookProof_FriedrichsExtension_FormDom_isUniformInducing_toComplL
-- name    : BookProof.FriedrichsExtension.FormDom.isUniformInducing_toComplL
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:24:58.64295+00:00
-- url     : https://prove2.me/theorems/f5227c9e-0d4d-44b1-8555-b92a5fab0d35
-- title:
--   The Lean 4 theorem `isUniformInducing_toComplL` in the `ChapterFriedrichsExtension` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `isUniformInducing_toComplL` in the `ChapterFriedrichsExtension` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFriedrichsExtension.lean

-- Generated from ChapterFriedrichsExtension.lean — theorem BookProof.FriedrichsExtension.FormDom.isUniformInducing_toComplL
import Mathlib
import Definitions.Def_ChapterFriedrichsExtension
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.HermiteGalerkin

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.FriedrichsExtension.FormDom.isUniformInducing_toComplL (P : PosSymOp F) :
    IsUniformInducing (UniformSpace.Completion.toComplL (𝕜 := ℂ) (E := FormDom P)) := by sorry
