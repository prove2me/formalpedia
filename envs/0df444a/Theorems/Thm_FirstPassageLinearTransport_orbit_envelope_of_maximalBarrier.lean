-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_orbit_envelope_of_maximalBarrier
-- name    : FirstPassageLinearTransport.orbit_envelope_of_maximalBarrier
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:06:17.080797+00:00
-- url     : https://prove2.me/theorems/2c8fa751-4fa2-52de-a397-746cd59eeb44
-- title:
--   First Passage Linear Transport: orbit envelope of maximal Barrier
-- statement:
--   The maximal barrier supplies the complete two-sided orbit envelope.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L541-L607
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L541-L607

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section

theorem FirstPassageLinearTransport.orbit_envelope_of_maximalBarrier
    {n k M : ℕ} {t : ℝ}
    (ht : 0 < t) (hM : 4 ≤ M) (hstart : 2 ≤ t * M)
    (hkM : k ≤ M) (hnShell : n ∈ dyadicShell M)
    (hreg : MaximalParityRegular n M (maximalBarrierHeight t M)) :
    centralOrbitScale k * (n : ℝ) ^ (1 - t) ≤ (orbit k n : ℝ) ∧
      (orbit k n : ℝ) ≤ centralOrbitScale k * (n : ℝ) ^ (1 + t) := by sorry
