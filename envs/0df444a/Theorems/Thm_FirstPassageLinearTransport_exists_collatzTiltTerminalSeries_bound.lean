-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_collatzTiltTerminalSeries_bound
-- name    : FirstPassageLinearTransport.exists_collatzTiltTerminalSeries_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:34:49.3841+00:00
-- url     : https://prove2.me/theorems/4b257e2d-eed4-4077-8c96-9d0c65b5d921
-- title:
--   First Passage Linear Transport: exists collatz Tilt Terminal Series bound
-- statement:
--   The First Passage Linear Transport construction uses the exists collatz Tilt Terminal Series bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1653-L1690
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1653-L1690

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.exists_collatzTiltTerminalSeries_bound :
    ∃ S : ℝ, 0 < S ∧ ∀ Q : ℕ,
      ∑ q ∈ Finset.range Q,
          ((q : ℝ) + 2) *
            Real.exp (-collatzTiltLambda * (q : ℝ)) ≤ S := by sorry
