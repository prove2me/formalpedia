-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_collatzMiddleIntervalMass_nonneg
-- name    : FirstPassageLinearTransport.collatzMiddleIntervalMass_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:55:59.965613+00:00
-- url     : https://prove2.me/theorems/1960d01d-f745-5346-b89f-7138ec66b1ca
-- title:
--   First Passage Linear Transport: collatz Middle Interval Mass nonneg
-- statement:
--   The First Passage Linear Transport construction uses the collatz Middle Interval Mass nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1616-L1625
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1616-L1625

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.collatzMiddleIntervalMass_nonneg (n : ℕ) (a : ℝ) :
    0 ≤ collatzMiddleIntervalMass n a := by sorry
