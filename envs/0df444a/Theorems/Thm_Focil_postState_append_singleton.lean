-- Prove2me | Theorems.Thm_Focil_postState_append_singleton
-- name    : Focil.postState_append_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:37:44.289177+00:00
-- url     : https://prove2.me/theorems/314afa15-ad02-425d-a3da-e062ed102a43
-- title:
--   Focil: post State append singleton
-- statement:
--   The post-state distributes over list concatenation: applying
--     a sequence then a single more transaction is the same as
--     applying that single transaction to the post-state of the
--     prefix. Direct from `List.foldl_append`.
--
--   Source: https://github.com/rahulbarmann/focil-lean4/blob/d6832793e6c5153e58079252e4a29c29bf1b7138/Focil/AccountState.lean#L186-L192
-- source:
--   https://github.com/rahulbarmann/focil-lean4/blob/d6832793e6c5153e58079252e4a29c29bf1b7138/Focil/AccountState.lean#L186-L192

import Definitions.Def_Focil_Types
import Definitions.Def_Focil_AccountState
set_option autoImplicit false
open Focil

theorem Focil.postState_append_singleton
    (initial : AccountState) (txs : List Transaction)
    (tx : Transaction) :
    postState initial (txs ++ [tx]) =
    applyTx (postState initial txs) tx := by sorry
