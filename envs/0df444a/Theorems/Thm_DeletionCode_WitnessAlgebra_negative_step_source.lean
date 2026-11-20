-- Prove2me | Theorems.Thm_DeletionCode_WitnessAlgebra_negative_step_source
-- name    : DeletionCode.WitnessAlgebra.negative_step_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:10:39.949695+00:00
-- url     : https://prove2.me/theorems/9262c8b0-7036-4a5e-b6f6-b02a12aeb4b6
-- title:
--   Witness Algebra: negative step source
-- statement:
--   A negative step coordinate must be present at its Boolean starting point.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessAlgebra.lean#L77-L85
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessAlgebra.lean#L77-L85

import Definitions.Def_DeletionCode_GeneratingBlocks
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Definitions.Def_DeletionCode_WitnessAlgebra
set_option autoImplicit true
open DeletionCode DeletionCode.WitnessAlgebra
open scoped BigOperators

theorem DeletionCode.WitnessAlgebra.negative_step_source {H : Type*} (p q : H → ℚ)
    (hp : BooleanVector p) (hq : BooleanVector q) (h : H)
    (hneg : (q - p) h = -1) : p h = 1 := by sorry
