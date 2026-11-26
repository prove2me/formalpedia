-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stageMap_le_power
-- name    : FirstPassageLinearTransport.stageMap_le_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:14:11.305588+00:00
-- url     : https://prove2.me/theorems/4b16c988-4f75-56cd-9e0e-5f1030e1432c
-- title:
--   First Passage Linear Transport: stage Map le power
-- statement:
--   One stopped stage satisfies the deterministic power contraction, with
--   the fixed constant only paying for the finite startup branch.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L157-L205
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L157-L205

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section

theorem FirstPassageLinearTransport.stageMap_le_power {r eta : ℝ} (p : StageSetup r eta)
    {n : ℕ} (hn : 0 < n) (hnW : n ∈ extendedWindow p) :
    (stageMap p n : ℝ) ≤ stageK p * (n : ℝ) ^ r := by sorry
