-- Prove2me | Theorems.Thm_BookProof_FriedrichsExtension_FormDom_dom_le_range
-- name    : BookProof.FriedrichsExtension.FormDom.dom_le_range
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-03T13:15:07.44474+00:00
-- url     : https://prove2.me/theorems/157f2354-c017-4a93-8ded-c6686265945e
-- title:
--   The Lean 4 theorem `dom_le_range` in the `ChapterFriedrichsExtension` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `dom_le_range` in the `ChapterFriedrichsExtension` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFriedrichsExtension.lean

-- Generated from ChapterFriedrichsExtension.lean — theorem BookProof.FriedrichsExtension.FormDom.dom_le_range
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

theorem BookProof.FriedrichsExtension.FormDom.dom_le_range (P : PosSymOp F) :
    P.dom ≤ LinearMap.range (friedrichsResolvent P : F →ₗ[ℂ] F) := by sorry
