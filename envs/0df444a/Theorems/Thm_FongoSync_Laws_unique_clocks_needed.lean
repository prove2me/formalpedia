-- Prove2me | Theorems.Thm_FongoSync_Laws_unique_clocks_needed
-- name    : FongoSync.Laws.unique_clocks_needed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:06:31.651857+00:00
-- url     : https://prove2.me/theorems/8dfb27e1-4cf1-4816-a7c4-03a29e140e55
-- title:
--   Laws: unique clocks needed
-- statement:
--   Without unique clocks the order of arrival can matter.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L117-L122
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L117-L122

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync

theorem FongoSync.Laws.unique_clocks_needed :
    let σ : String → String → Strategy := fun _ _ => .lww
    let a : Change Value := ⟨"things", 0, "title", .int 1, ⟨1, 0, 1⟩⟩
    let b : Change Value := ⟨"things", 0, "title", .int 2, ⟨1, 0, 1⟩⟩
    merged σ [a, b] ("things", 0, "title") ≠ merged σ [b, a] ("things", 0, "title") := by sorry
