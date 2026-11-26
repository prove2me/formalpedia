-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
-- name    : FirstPassageLinearTransport.mem_transportedSources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:00:06.790852+00:00
-- url     : https://prove2.me/theorems/ed2f2ca4-62d1-4df6-9f83-4aa9a2145bf4
-- title:
--   First Passage Linear Transport: mem transported Sources
-- statement:
--   The First Passage Linear Transport construction uses the mem transported Sources property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Transport.lean#L108-L132
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Transport.lean#L108-L132

import Definitions.Def_FirstPassageLinearTransport_FirstPassage
import Definitions.Def_FirstPassageLinearTransport_Transport
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.mem_transportedSources {M Y H n : ℕ} {B : Finset ℕ} :
    n ∈ transportedSources M Y H B ↔
      n ∈ dyadicShell M ∧
        ∃ h : ℕ, 1 ≤ h ∧ h ≤ H ∧ IsFirstPassage Y n h ∧ orbit h n ∈ B := by sorry
