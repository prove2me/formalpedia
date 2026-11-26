-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_reciprocal_finite_multiplicative_maximum
-- name    : FirstPassageLinearTransport.reciprocal_finite_multiplicative_maximum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:32:48.647512+00:00
-- url     : https://prove2.me/theorems/cc223679-2f39-4aaa-8c15-415bd85e3f2d
-- title:
--   First Passage Linear Transport: reciprocal finite multiplicative maximum
-- statement:
--   Manuscript Lemma B.5: reciprocal lower and upper bounds for the finite
--   multiplicative maximum.  All probabilities are exact finite-word weights.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L3233-L3251
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L3233-L3251

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.reciprocal_finite_multiplicative_maximum
    {u : ℝ} (hu : 1 ≤ u) {r : ℕ} (hr : 0 < r)
    (hlog : Real.log u ≤
      reciprocalMaximumEpsilon * (r : ℝ) * Real.log 3) :
    (2 / (3 * u)) *
        (1 - reciprocalMaximumConstant / (r : ℝ)) ≤
      (multiplicativeHitCount u r 1 : ℝ) / (2 : ℝ) ^ r ∧
    (multiplicativeHitCount u r 1 : ℝ) / (2 : ℝ) ^ r ≤ u⁻¹ := by sorry
