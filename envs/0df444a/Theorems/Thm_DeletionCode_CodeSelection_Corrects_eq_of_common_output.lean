-- Prove2me | Theorems.Thm_DeletionCode_CodeSelection_Corrects_eq_of_common_output
-- name    : DeletionCode.CodeSelection.Corrects.eq_of_common_output
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:42:46.359902+00:00
-- url     : https://prove2.me/theorems/ba13e3dd-57a1-4052-bd43-49637ca658a9
-- title:
--   Corrects: eq of common output
-- statement:
--   Thus any shared output uniquely determines a codeword, with the edit
--   relation exactly the one used by the manuscript's conflict graph.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CodeSelection.lean#L27-L32
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CodeSelection.lean#L27-L32

import Definitions.Def_DeletionCode_BipartiteSelection
import Definitions.Def_DeletionCode_ConflictGraphWitness
import Definitions.Def_DeletionCode_CodeSelection
set_option autoImplicit true
open DeletionCode DeletionCode.CodeSelection
open HeaderRecovery ConflictGraphWitness BipartiteSelection
variable {n k : ℕ}

theorem DeletionCode.CodeSelection.Corrects.eq_of_common_output {t : ℕ} {C : Finset (Bits n)} (hC : Corrects t C)
    {x y : Bits n} (hx : x ∈ C) (hy : y ∈ C) (output : List Bool)
    (hxo : EditAlignment.WithinEdits t (List.ofFn x) output)
    (hyo : EditAlignment.WithinEdits t (List.ofFn y) output) : x = y := by sorry
