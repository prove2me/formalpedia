-- Prove2me | Theorems.Thm_DeletionCode_PaperParameters_L_eq
-- name    : DeletionCode.PaperParameters.L_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:30:09.187536+00:00
-- url     : https://prove2.me/theorems/0bbbe48b-c9eb-4859-946a-2974a08015ba
-- title:
--   Paper Parameters: L eq
-- statement:
--   The Paper Parameters construction uses the L eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PaperParameters.lean#L19-L21
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PaperParameters.lean#L19-L21

import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Analysis.Asymptotics.Defs
import Definitions.Def_DeletionCode_PaperParameters
set_option autoImplicit true
open DeletionCode DeletionCode.PaperParameters
open Filter Asymptotics
open scoped Topology

theorem DeletionCode.PaperParameters.L_eq (n : ℕ) : L n = 6 * Nat.clog 2 n + 9 := by sorry
