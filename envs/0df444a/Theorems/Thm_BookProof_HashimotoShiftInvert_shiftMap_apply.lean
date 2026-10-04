-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_shiftMap_apply
-- name    : BookProof.HashimotoShiftInvert.shiftMap_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-03T14:09:08.825274+00:00
-- url     : https://prove2.me/theorems/1ba530a2-ba8c-4fab-9036-22f8cd74acef
-- title:
--   The Lean 4 theorem `shiftMap_apply` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.HashimotoShiftInvert.shiftMap_apply` from the timepiece Lean 4 formalization (source chapter `BookProof/ChapterHashimotoShiftInvert.lean`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoShiftInvert.lean

-- Generated from ChapterHashimotoShiftInvert.lean — theorem BookProof.HashimotoShiftInvert.shiftMap_apply
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterComplexShiftCore
open BookProof.HashimotoShiftInvert

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology

theorem BookProof.HashimotoShiftInvert.shiftMap_apply (A : Dom →ₗ[ℂ] F) (γ : ℝ) (x : Dom) :
    shiftMap A γ x = A x + (γ : ℂ) • (x : F) := by sorry
