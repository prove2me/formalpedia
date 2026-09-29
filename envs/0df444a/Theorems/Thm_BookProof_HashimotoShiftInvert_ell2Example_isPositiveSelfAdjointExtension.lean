-- Prove2me | Theorems.Thm_BookProof_HashimotoShiftInvert_ell2Example_isPositiveSelfAdjointExtension
-- name    : BookProof.HashimotoShiftInvert.ell2Example_isPositiveSelfAdjointExtension
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:31:48.043987+00:00
-- url     : https://prove2.me/theorems/be8e3a0f-b2c0-485a-b3a1-974871e7db04
-- title:
--   The Lean 4 theorem `ell2Example_isPositiveSelfAdjointExtension` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ell2Example_isPositiveSelfAdjointExtension` in the `ChapterHashimotoShiftInvert` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHashimotoShiftInvert.lean

-- Generated from ChapterHashimotoShiftInvert.lean — theorem BookProof.HashimotoShiftInvert.ell2Example_isPositiveSelfAdjointExtension
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
open BookProof.HashimotoShiftInvert



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology

theorem BookProof.HashimotoShiftInvert.ell2Example_isPositiveSelfAdjointExtension :
    IsPositiveSelfAdjointExtension ell2ExampleMatrix ell2UnboundedExample := by sorry
