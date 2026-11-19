-- Prove2me | Theorems.Thm_DeletionCode_MaximalRuns_constantOn_block
-- name    : DeletionCode.MaximalRuns.constantOn_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:21:50.771059+00:00
-- url     : https://prove2.me/theorems/e7b9ff74-403e-4253-8122-a1619158ddcd
-- title:
--   Maximal Runs: constant On block
-- statement:
--   Every index in a displayed constant block reads its actual bit.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/MaximalRuns.lean#L85-L95
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/MaximalRuns.lean#L85-L95

import Definitions.Def_DeletionCode_UniqueRuns
import Definitions.Def_DeletionCode_SingleEditScripts
import Definitions.Def_DeletionCode_MaximalRuns
set_option autoImplicit true
open DeletionCode DeletionCode.MaximalRuns
open Windows CatalogueWords UniqueRuns

theorem DeletionCode.MaximalRuns.constantOn_block (pre suffix : List Bool) (rho : ℕ) (bit : Bool) :
    ConstantOn (listLetters (pre ++ List.replicate rho bit ++ suffix)) pre.length rho bit := by sorry
