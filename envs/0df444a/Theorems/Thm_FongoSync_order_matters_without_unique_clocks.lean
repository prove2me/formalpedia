-- Prove2me | Theorems.Thm_FongoSync_order_matters_without_unique_clocks
-- name    : FongoSync.order_matters_without_unique_clocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:01:05.345445+00:00
-- url     : https://prove2.me/theorems/b97600cd-f1a4-4162-bba7-8d85ce75b265
-- title:
--   Fongo Sync: order matters without unique clocks
-- statement:
--   Unique clocks are needed: two different `Lww` values at one clock give an answer that depends
--   on the order they arrived in.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Examples.lean#L60-L65
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Examples.lean#L60-L65

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Examples
set_option autoImplicit false
open FongoSync

theorem FongoSync.order_matters_without_unique_clocks :
    let σ : String → String → Strategy := fun _ _ => .lww
    let a : Change Value := ⟨"things", 0, "title", .int 1, ⟨1, 0, 1⟩⟩
    let b : Change Value := ⟨"things", 0, "title", .int 2, ⟨1, 0, 1⟩⟩
    merged σ [a, b] ("things", 0, "title") ≠ merged σ [b, a] ("things", 0, "title") := by sorry
