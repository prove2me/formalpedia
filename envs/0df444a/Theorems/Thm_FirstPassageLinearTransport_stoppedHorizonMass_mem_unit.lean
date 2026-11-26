-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stoppedHorizonMass_mem_unit
-- name    : FirstPassageLinearTransport.stoppedHorizonMass_mem_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:28:52.052001+00:00
-- url     : https://prove2.me/theorems/471b03e9-69d5-497f-ae7c-9368a5ef2f8f
-- title:
--   First Passage Linear Transport: stopped Horizon Mass mem unit
-- statement:
--   The First Passage Linear Transport construction uses the stopped Horizon Mass mem unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L147-L163
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L147-L163

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.stoppedHorizonMass_mem_unit
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (x : Bool → ℝ) (lo hi : ℝ) :
    ∀ r z, 0 ≤ stoppedHorizonMass p x lo hi r z ∧
      stoppedHorizonMass p x lo hi r z ≤ 1 := by sorry
