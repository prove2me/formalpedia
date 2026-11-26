-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_threeQuarterLowerTailMass_le
-- name    : FirstPassageLinearTransport.threeQuarterLowerTailMass_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:37:04.1458+00:00
-- url     : https://prove2.me/theorems/c2124a3d-ca2a-4e84-94ba-af4b971ae104
-- title:
--   First Passage Linear Transport: three Quarter Lower Tail Mass le
-- statement:
--   Finite Chebyshev bound for the `3/4`-weighted support count.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2809-L2850
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2809-L2850

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.threeQuarterLowerTailMass_le
    {eps : ℝ} (heps : 0 < eps) {r : ℕ} (hr : 0 < r) :
    threeQuarterLowerTailMass eps r ≤
      3 / (16 * eps ^ 2 * (r : ℝ)) := by sorry
