-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
-- name    : FirstPassageLinearTransport.mem_taggedFiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:59:35.509323+00:00
-- url     : https://prove2.me/theorems/ad120db6-f21d-5a78-945b-376058a6993f
-- title:
--   First Passage Linear Transport: mem tagged Fiber
-- statement:
--   The First Passage Linear Transport construction uses the mem tagged Fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L345-L349
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L345-L349

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.mem_taggedFiber {M Y h y n : ℕ} :
    n ∈ taggedFiber M Y h y ↔
      n ∈ dyadicShell M ∧ IsFirstPassage Y n h ∧ orbit h n = y := by sorry
