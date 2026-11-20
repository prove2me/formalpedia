-- Prove2me | Theorems.Thm_DeletionCode_WitnessAlgebra_generating_append
-- name    : DeletionCode.WitnessAlgebra.generating_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:17.706305+00:00
-- url     : https://prove2.me/theorems/e9c7919d-b734-4f4c-914e-0331cb1e08bb
-- title:
--   Witness Algebra: generating append
-- statement:
--   The generating invariant at an append, as in the bounded-witness proof.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessAlgebra.lean#L88-L98
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessAlgebra.lean#L88-L98

import Definitions.Def_DeletionCode_GeneratingBlocks
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Definitions.Def_DeletionCode_WitnessAlgebra
set_option autoImplicit true
open DeletionCode DeletionCode.WitnessAlgebra
open scoped BigOperators

theorem DeletionCode.WitnessAlgebra.generating_append {H : Type*} (v p q : H → ℚ) (S : Set (H → ℚ))
    (hp : BooleanVector p) (hq : BooleanVector q)
    (hspan : p - v ∈ Submodule.span ℚ S) (h : H)
    (hneg : (q - p) h = -1) : v h ≠ 0 ∨ ∃ w ∈ S, w h ≠ 0 := by sorry
