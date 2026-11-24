-- Prove2me | Theorems.Thm_FongoSync_view_swap
-- name    : FongoSync.view_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:59:24.398811+00:00
-- url     : https://prove2.me/theorems/960b2fa0-a511-436d-8d29-165774a91aae
-- title:
--   Fongo Sync: view swap
-- statement:
--   Swapping two neighbouring changes leaves the view the same, if either is an alias or they do
--   not write one register at one clock with different values.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/View.lean#L306-L314
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/View.lean#L306-L314

import Definitions.Def_FongoSync_State
import Definitions.Def_FongoSync_Alias
import Definitions.Def_FongoSync_GidSet
import Definitions.Def_FongoSync_View
set_option autoImplicit false
open FongoSync
open Std Classical
set_option linter.unusedSectionVars false

theorem FongoSync.view_swap (sc : Schema) (pre post : List (Change Value)) (a b : Change Value)
    (h : a.field = ALIAS ∨ b.field = ALIAS ∨ Compatible a b) :
    view sc (pre ++ a :: b :: post) = view sc (pre ++ b :: a :: post) := by sorry
