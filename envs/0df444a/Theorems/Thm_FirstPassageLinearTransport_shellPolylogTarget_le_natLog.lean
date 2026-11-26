-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shellPolylogTarget_le_natLog
-- name    : FirstPassageLinearTransport.shellPolylogTarget_le_natLog
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:43:50.232108+00:00
-- url     : https://prove2.me/theorems/8118fef5-218a-5fe9-bc37-8f47f25c36ad
-- title:
--   First Passage Linear Transport: shell Polylog Target le nat Log
-- statement:
--   Conversion of the shell target to the paper's natural-logarithm target.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/PolylogTarget.lean#L44-L78
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/PolylogTarget.lean#L44-L78

import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_PolylogTarget
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.shellPolylogTarget_le_natLog
    {A : ℝ} (hA : 0 ≤ A) {M n : ℕ}
    (hnShell : n ∈ dyadicShell M) (hlogn : 1 ≤ Real.log n) :
    2 * (((M : ℝ) + 2) ^ A) ≤
      fixedPolylogTargetConstant A * (Real.log n) ^ A := by sorry
