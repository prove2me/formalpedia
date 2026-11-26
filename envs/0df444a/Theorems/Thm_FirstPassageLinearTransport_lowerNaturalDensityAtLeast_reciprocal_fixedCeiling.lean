-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_lowerNaturalDensityAtLeast_reciprocal_fixedCeiling
-- name    : FirstPassageLinearTransport.lowerNaturalDensityAtLeast_reciprocal_fixedCeiling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:34:03.343126+00:00
-- url     : https://prove2.me/theorems/56d24dfd-78e4-55de-801d-7c1271df190e
-- title:
--   First Passage Linear Transport: lower Natural Density At Least reciprocal fixed Ceiling
-- statement:
--   Manuscript Proposition 8.1.  The hypothesis is the exact
--   prefix-unreachability consequence of `f(n) = o(n)` consumed by the proof.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ReciprocalHeightObstruction.lean#L550-L607
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ReciprocalHeightObstruction.lean#L550-L607

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.lowerNaturalDensityAtLeast_reciprocal_fixedCeiling
    {u : ℝ} (hu : 1 ≤ u) {f : ℕ → ℝ}
    (hsublinear : ∀ h : ℕ,
      ∀ᶠ n : ℕ in Filter.atTop,
        f n < (n : ℝ) / (2 : ℝ) ^ h) :
    LowerNaturalDensityAtLeast (targetHeightFailureSet f u) (2 / (3 * u)) := by sorry
