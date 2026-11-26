-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_mem_initialWindowGood_of_mem_extended_of_large
-- name    : FirstPassageLinearTransport.mem_initialWindowGood_of_mem_extended_of_large
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:08:16.63289+00:00
-- url     : https://prove2.me/theorems/21526440-693a-446d-bca8-919a9c37e18d
-- title:
--   First Passage Linear Transport: mem initial Window Good of mem extended of large
-- statement:
--   The First Passage Linear Transport construction uses the mem initial Window Good of mem extended of large property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L119-L136
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L119-L136

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.mem_initialWindowGood_of_mem_extended_of_large
    {r eta : ℝ} (p : StageSetup r eta) {n : ℕ}
    (hn : n ∈ extendedWindow p) (hlarge : p.M0 ≤ Nat.log 2 n) :
    n ∈ initialWindowGood eta := by sorry
