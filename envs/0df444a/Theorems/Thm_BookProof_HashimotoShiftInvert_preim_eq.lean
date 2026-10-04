-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_preim_eq
-- name    : BookProof.HashimotoShiftInvert.preim_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-03T14:09:00.00747+00:00
-- url     : https://prove2.me/theorems/c4cee274-22d6-4a22-b4cf-042869a25191
-- title:
--   The Lean 4 theorem `preim_eq` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.HashimotoShiftInvert.preim_eq` from the timepiece Lean 4 formalization (source chapter `BookProof/ChapterHashimotoShiftInvert.lean`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoShiftInvert.lean

-- Generated from ChapterHashimotoShiftInvert.lean — theorem BookProof.HashimotoShiftInvert.preim_eq
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterComplexShiftCore
open BookProof.HashimotoShiftInvert

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology

theorem BookProof.HashimotoShiftInvert.preim_eq (R : F →L[ℂ] F) (hinj : Function.Injective R)
    (y : LinearMap.range (R : F →ₗ[ℂ] F)) {u : F} (hu : R u = (y : F)) : preim R y = u := by sorry
