-- Prove2me | Theorems.Thm_DeletionCode_WitnessAlgebra_scalar_multiple_eq_or_neg
-- name    : DeletionCode.WitnessAlgebra.scalar_multiple_eq_or_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:11:53.607788+00:00
-- url     : https://prove2.me/theorems/2e72b075-ec3b-4342-b09b-4c1611f7c295
-- title:
--   Witness Algebra: scalar multiple eq or neg
-- statement:
--   A one-term nonzero relation is precisely a previously seen rule or its negative.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessAlgebra.lean#L125-L130
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessAlgebra.lean#L125-L130

import Definitions.Def_DeletionCode_GeneratingBlocks
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Definitions.Def_DeletionCode_WitnessAlgebra
set_option autoImplicit true
open DeletionCode DeletionCode.WitnessAlgebra
open scoped BigOperators

theorem DeletionCode.WitnessAlgebra.scalar_multiple_eq_or_neg {H : Type*} (g w : H → ℚ) (a : ℚ)
    (hg : SignedUnitVector g) (hw : SignedUnitVector w)
    (hg0 : g ≠ 0) (ha : a ≠ 0) (hrel : w = a • g) : w = g ∨ w = -g := by sorry
