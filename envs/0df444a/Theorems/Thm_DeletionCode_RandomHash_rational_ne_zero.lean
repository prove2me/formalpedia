-- Prove2me | Theorems.Thm_DeletionCode_RandomHash_rational_ne_zero
-- name    : DeletionCode.RandomHash.rational_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:37:24.384561+00:00
-- url     : https://prove2.me/theorems/a96bbb6d-6f88-47e3-be88-c449a3daf8e9
-- title:
--   Random Hash: rational ne zero
-- statement:
--   The Random Hash construction uses the rational ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L62-L69
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L62-L69

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]
omit [Fintype I]

theorem DeletionCode.RandomHash.rational_ne_zero (w : I → ℤ) (hw : w ≠ 0) : (fun i => (w i : ℚ)) ≠ 0 := by sorry
