-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stoppedUpperMass_mem_unit
-- name    : FirstPassageLinearTransport.stoppedUpperMass_mem_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:30:35.002912+00:00
-- url     : https://prove2.me/theorems/30bd4277-7294-566d-8d9f-1b60af9d502a
-- title:
--   First Passage Linear Transport: stopped Upper Mass mem unit
-- statement:
--   The First Passage Linear Transport construction uses the stopped Upper Mass mem unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L127-L145
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L127-L145

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.stoppedUpperMass_mem_unit
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (x : Bool → ℝ) (lo hi : ℝ) :
    ∀ r z, 0 ≤ stoppedUpperMass p x lo hi r z ∧
      stoppedUpperMass p x lo hi r z ≤ 1 := by sorry
