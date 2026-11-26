-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_barrierHitCount_le_legendre
-- name    : FirstPassageLinearTransport.barrierHitCount_le_legendre
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:11:52.76727+00:00
-- url     : https://prove2.me/theorems/5230a20f-8825-530b-b48a-1267c34bf2f6
-- title:
--   First Passage Linear Transport: barrier Hit Count le legendre
-- statement:
--   Exact barrier bound expressed by the unoptimized Legendre rate.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/EntropyBarrier.lean#L91-L101
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/EntropyBarrier.lean#L91-L101

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.barrierHitCount_le_legendre
    (t θ : ℝ) (M : ℕ) (ht : 0 ≤ t) (hθ : 0 ≤ θ) :
    (barrierHitCount (2 * t * M) M 0 : ℝ) ≤
      (2 : ℝ) ^ (M + 1) *
        Real.exp (-((M : ℝ) * booleanLegendreRate t θ)) := by sorry
