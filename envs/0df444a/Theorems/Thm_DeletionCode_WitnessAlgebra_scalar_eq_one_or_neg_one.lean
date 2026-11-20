-- Prove2me | Theorems.Thm_DeletionCode_WitnessAlgebra_scalar_eq_one_or_neg_one
-- name    : DeletionCode.WitnessAlgebra.scalar_eq_one_or_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:11:51.661781+00:00
-- url     : https://prove2.me/theorems/eac1d35c-559f-4716-b36e-39ceaf6e3f92
-- title:
--   Witness Algebra: scalar eq one or neg one
-- statement:
--   Signed vectors cannot be distinct non-unit scalar multiples of each other.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessAlgebra.lean#L101-L122
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessAlgebra.lean#L101-L122

import Definitions.Def_DeletionCode_GeneratingBlocks
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Definitions.Def_DeletionCode_WitnessAlgebra
set_option autoImplicit true
open DeletionCode DeletionCode.WitnessAlgebra
open scoped BigOperators

theorem DeletionCode.WitnessAlgebra.scalar_eq_one_or_neg_one {H : Type*} (g w : H → ℚ) (a : ℚ)
    (hg : SignedUnitVector g) (hw : SignedUnitVector w)
    (hg0 : g ≠ 0) (ha : a ≠ 0) (hrel : w = a • g) : a = 1 ∨ a = -1 := by sorry
