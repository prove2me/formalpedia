-- Prove2me | Theorems.Thm_DeletionCode_EditLocality_origin_in_source_interval
-- name    : DeletionCode.EditLocality.origin_in_source_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:39:17.558814+00:00
-- url     : https://prove2.me/theorems/668b612e-a7f9-44e4-a4c7-e258c00fd6f6
-- title:
--   Edit Locality: origin in source interval
-- statement:
--   Surviving letters of a local output segment have source indices inside
--   its original interval. This is derived from the actual edit's origin map.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/EditLocality.lean#L30-L55
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/EditLocality.lean#L30-L55

import Definitions.Def_DeletionCode_EditRigidity
import Mathlib.Order.Interval.Set.Basic
import Definitions.Def_DeletionCode_EditLocality
set_option autoImplicit true
open DeletionCode DeletionCode.EditLocality
open Windows HeaderRecovery SingleEditOrigins

theorem DeletionCode.EditLocality.origin_in_source_interval (e : Edit) (start len i r : ℕ)
    (he : Inside e start len) (hstart : start ≤ i)
    (hend : i < start + e.outputLength len) (hr : e.origin i = some r) :
    start ≤ r ∧ r < start + len := by sorry
