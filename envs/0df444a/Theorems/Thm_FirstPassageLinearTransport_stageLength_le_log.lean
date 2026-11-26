-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stageLength_le_log
-- name    : FirstPassageLinearTransport.stageLength_le_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:20:04.926268+00:00
-- url     : https://prove2.me/theorems/675a8beb-8b9c-4e1e-9a33-ef669588157c
-- title:
--   First Passage Linear Transport: stage Length le log
-- statement:
--   The stopped block length never exceeds the current binary shell index.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L134-L141
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L134-L141

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section

theorem FirstPassageLinearTransport.stageLength_le_log {r eta : ℝ} (p : StageSetup r eta)
    {n : ℕ} (hn : 0 < n) (hnW : n ∈ extendedWindow p) :
    stageLength p n ≤ Nat.log 2 n := by sorry
