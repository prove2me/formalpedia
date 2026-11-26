-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_sum_threeQuarter_centered_sq
-- name    : FirstPassageLinearTransport.sum_threeQuarter_centered_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:36:53.916269+00:00
-- url     : https://prove2.me/theorems/210da13c-29bd-514a-bbdb-b1c65d376987
-- title:
--   First Passage Linear Transport: sum three Quarter centered sq
-- statement:
--   The centered support count has variance `3r/16` under the `3/4`
--   Bernoulli product weighting.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2764-L2798
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2764-L2798

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.sum_threeQuarter_centered_sq :
    ∀ r : ℕ,
      ∑ v : Fin r → Bool,
          bernoulliWordWeight (3 / 4) v *
            (((boolSupport v).card : ℝ) - 3 * (r : ℝ) / 4) ^ 2 =
        3 * (r : ℝ) / 16 := by sorry
