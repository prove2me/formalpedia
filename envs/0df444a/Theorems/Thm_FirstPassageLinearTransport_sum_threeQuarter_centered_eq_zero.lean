-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_sum_threeQuarter_centered_eq_zero
-- name    : FirstPassageLinearTransport.sum_threeQuarter_centered_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:58:00.843597+00:00
-- url     : https://prove2.me/theorems/2e844ff3-0c39-4550-8637-fd467613a7db
-- title:
--   First Passage Linear Transport: sum three Quarter centered eq zero
-- statement:
--   The centered support count has mean zero under the `3/4` Bernoulli
--   product weighting.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2733-L2760
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2733-L2760

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.sum_threeQuarter_centered_eq_zero :
    ∀ r : ℕ,
      ∑ v : Fin r → Bool,
          bernoulliWordWeight (3 / 4) v *
            (((boolSupport v).card : ℝ) - 3 * (r : ℝ) / 4) = 0 := by sorry
