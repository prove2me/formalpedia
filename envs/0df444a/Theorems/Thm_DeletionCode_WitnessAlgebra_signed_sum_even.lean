-- Prove2me | Theorems.Thm_DeletionCode_WitnessAlgebra_signed_sum_even
-- name    : DeletionCode.WitnessAlgebra.signed_sum_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:11:57.349179+00:00
-- url     : https://prove2.me/theorems/59cea84e-25f8-4621-9b47-af44ccb86d00
-- title:
--   Witness Algebra: signed sum even
-- statement:
--   A zero-sum sequence of signed independent vectors has even length.
--   This is the algebraic obstruction to traversing an odd closed walk using only ±G.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessAlgebra.lean#L134-L177
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessAlgebra.lean#L134-L177

import Definitions.Def_DeletionCode_GeneratingBlocks
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Definitions.Def_DeletionCode_WitnessAlgebra
set_option autoImplicit true
open DeletionCode DeletionCode.WitnessAlgebra
open scoped BigOperators

theorem DeletionCode.WitnessAlgebra.signed_sum_even {I J V : Type*} [Fintype I] [Fintype J]
    [AddCommGroup V] [Module ℚ V] (G : I → V) (hG : LinearIndependent ℚ G)
    (label : J → I) (positive : J → Prop) [DecidablePred positive]
    (hsum : (∑ j, (if positive j then (1 : ℚ) else -1) • G (label j)) = 0) :
    Even (Fintype.card J) := by sorry
