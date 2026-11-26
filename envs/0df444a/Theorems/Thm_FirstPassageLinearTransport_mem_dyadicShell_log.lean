-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell_log
-- name    : FirstPassageLinearTransport.mem_dyadicShell_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:12:47.758699+00:00
-- url     : https://prove2.me/theorems/e7a971b4-1d38-5b7f-bbcd-ef877e0a91eb
-- title:
--   First Passage Linear Transport: mem dyadic Shell log
-- statement:
--   Every positive integer lies in the shell indexed by its binary log.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L127-L131
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L127-L131

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section

theorem FirstPassageLinearTransport.mem_dyadicShell_log {n : ℕ} (hn : 0 < n) :
    n ∈ dyadicShell (Nat.log 2 n) := by sorry
