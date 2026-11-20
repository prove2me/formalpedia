-- Prove2me | Theorems.Thm_DeletionCode_WitnessAlgebra_span_support
-- name    : DeletionCode.WitnessAlgebra.span_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:11:45.13888+00:00
-- url     : https://prove2.me/theorems/724d7ff1-a1af-4ade-b53c-388c4942ede8
-- title:
--   Witness Algebra: span support
-- statement:
--   A nonzero coordinate in the span occurs in some spanning vector.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessAlgebra.lean#L68-L74
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessAlgebra.lean#L68-L74

import Definitions.Def_DeletionCode_GeneratingBlocks
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Definitions.Def_DeletionCode_WitnessAlgebra
set_option autoImplicit true
open DeletionCode DeletionCode.WitnessAlgebra
open scoped BigOperators

theorem DeletionCode.WitnessAlgebra.span_support {H : Type*} (S : Set (H → ℚ)) (u : H → ℚ)
    (hu : u ∈ Submodule.span ℚ S) (h : H) (hne : u h ≠ 0) :
    ∃ w ∈ S, w h ≠ 0 := by sorry
