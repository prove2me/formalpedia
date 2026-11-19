-- Prove2me | Theorems.Thm_DeletionCode_RecordBounds_loadRoots_bounded
-- name    : DeletionCode.RecordBounds.loadRoots_bounded
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:17:00.83172+00:00
-- url     : https://prove2.me/theorems/fff58427-c549-4082-bea0-cabd4b814c5b
-- title:
--   Record Bounds: load Roots bounded
-- statement:
--   The Record Bounds construction uses the load Roots bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RecordBounds.lean#L135-L155
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RecordBounds.lean#L135-L155

import Definitions.Def_DeletionCode_GeneratingRecovery
import Definitions.Def_DeletionCode_RecordCodec
import Definitions.Def_DeletionCode_RecordBounds
set_option autoImplicit true
open DeletionCode DeletionCode.RecordBounds
open Windows PartialWords HeaderRecovery PathMemory ConcreteDecoder RecordCodec
variable {B : Type*} [DecidableEq B]

theorem DeletionCode.RecordBounds.loadRoots_bounded (x : Letters) (n k : ℕ) (header : B → Header)
    (hlo : ∀ b, 1 ≤ (header b).rho) (hhi : ∀ b, (header b).rho ≤ k + 1)
    (roots : List (B × ℕ)) (mem result : Bank B)
    (hs : loadRoots x n k header mem roots = some result) :
    ∀ b a, (b, a) ∈ roots → a < n := by sorry
