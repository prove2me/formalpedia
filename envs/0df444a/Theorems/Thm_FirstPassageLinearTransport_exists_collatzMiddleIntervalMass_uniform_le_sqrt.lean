-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_collatzMiddleIntervalMass_uniform_le_sqrt
-- name    : FirstPassageLinearTransport.exists_collatzMiddleIntervalMass_uniform_le_sqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:34:43.03554+00:00
-- url     : https://prove2.me/theorems/9fa165fe-27a2-4b09-9d7e-4db7c222b352
-- title:
--   First Passage Linear Transport: exists collatz Middle Interval Mass uniform le sqrt
-- statement:
--   The First Passage Linear Transport construction uses the exists collatz Middle Interval Mass uniform le sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1627-L1631
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1627-L1631

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.exists_collatzMiddleIntervalMass_uniform_le_sqrt :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ a : ℝ, 0 < n →
      collatzMiddleIntervalMass n a ≤ C / Real.sqrt n := by sorry
