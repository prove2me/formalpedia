-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_collatzMiddleIntervalMass_le_sqrt
-- name    : FirstPassageLinearTransport.exists_collatzMiddleIntervalMass_le_sqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:34:39.194737+00:00
-- url     : https://prove2.me/theorems/f35133cb-9ba3-44a2-a33d-6ddf8e4aef05
-- title:
--   First Passage Linear Transport: exists collatz Middle Interval Mass le sqrt
-- statement:
--   The middle-block terminal interval costs at most one tilted binomial
--   atom.  This is the lattice component of the three-block timeout estimate.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1517-L1565
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1517-L1565

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.exists_collatzMiddleIntervalMass_le_sqrt :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ a : ℝ, 0 < n →
      ∑ v : Fin n → Bool,
          bernoulliWordWeight collatzTilt v *
            collatzMiddleIntervalIndicator a v ≤
        C / Real.sqrt n := by sorry
