-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_normalized_card_shellTargetHeightFailure_ge_reciprocal
-- name    : FirstPassageLinearTransport.normalized_card_shellTargetHeightFailure_ge_reciprocal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:54:29.710061+00:00
-- url     : https://prove2.me/theorems/1d7d9f2e-18d0-443a-ae4d-c54cdfeca184
-- title:
--   First Passage Linear Transport: normalized card shell Target Height Failure ge reciprocal
-- statement:
--   Exact finite moving-shell obstruction.  The target-unreachability and
--   logarithmic-slope hypotheses can be discharged asymptotically by taking, for
--   example, `h = floor (M/2)` and subexponential shell targets and ceilings.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ReciprocalHeightObstruction.lean#L251-L272
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ReciprocalHeightObstruction.lean#L251-L272

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.normalized_card_shellTargetHeightFailure_ge_reciprocal
    {M h : ℕ} (hhM : h ≤ M) (hh : 0 < h)
    {u : ℝ} (hu : 1 ≤ u)
    (hlog : Real.log u ≤
      reciprocalMaximumEpsilon * (h : ℝ) * Real.log 3)
    {f : ℕ → ℝ}
    (htarget : ∀ n : ℕ, n ∈ dyadicShell M →
      f n < (n : ℝ) / (2 : ℝ) ^ h) :
    (2 / (3 * u)) *
        (1 - reciprocalMaximumConstant / (h : ℝ)) ≤
      ((shellTargetHeightFailure M f u).card : ℝ) / (2 : ℝ) ^ M := by sorry
