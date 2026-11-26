-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_landingBad_density_le
-- name    : FirstPassageLinearTransport.landingBad_density_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:13:28.585106+00:00
-- url     : https://prove2.me/theorems/e8c0cbfa-2ab9-4cf5-8ae3-c7a413ee6649
-- title:
--   First Passage Linear Transport: landing Bad density le
-- statement:
--   A shell-cardinality estimate becomes the sum of its one-point boundary
--   and entropy-density terms after division by the landing-shell size.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TerminalProfile.lean#L71-L93
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TerminalProfile.lean#L71-L93

import Definitions.Def_FirstPassageLinearTransport_TerminalTail
import Definitions.Def_FirstPassageLinearTransport_TerminalProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.landingBad_density_le
    {q : ℕ} (hq : 1 ≤ q) {t b : ℝ}
    (hcard : ((landingBad q t).card : ℝ) ≤
      1 + (2 : ℝ) ^ q *
        Real.exp (-(((q - 1 : ℕ) : ℝ) * b))) :
    ((landingBad q t).card : ℝ) / (2 : ℝ) ^ q ≤
      Real.exp (-(Real.log 2 * (q : ℝ))) +
        Real.exp b * Real.exp (-(b * (q : ℝ))) := by sorry
