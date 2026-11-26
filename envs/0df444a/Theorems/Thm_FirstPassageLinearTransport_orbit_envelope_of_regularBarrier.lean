-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_orbit_envelope_of_regularBarrier
-- name    : FirstPassageLinearTransport.orbit_envelope_of_regularBarrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:12:55.572832+00:00
-- url     : https://prove2.me/theorems/65ebbded-0e61-5c7f-b144-d9209e447ac4
-- title:
--   First Passage Linear Transport: orbit envelope of regular Barrier
-- statement:
--   Deterministic envelope from any fixed maximal-parity barrier once the two
--   phase inequalities and the affine-correction absorption are supplied.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AdjustableEnvelope.lean#L52-L76
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AdjustableEnvelope.lean#L52-L76

import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.orbit_envelope_of_regularBarrier
    {n k M : ℕ} {h t : ℝ}
    (hkM : k ≤ M) (hnShell : n ∈ dyadicShell M)
    (hreg : MaximalParityRegular n M h)
    (hphase : (3 : ℝ) ^ h ≤ (n : ℝ) ^ t)
    (hphaseTwo : 2 * (3 : ℝ) ^ h ≤ (n : ℝ) ^ t)
    (hcorrAbsorb :
      2 * ((2 + Real.sqrt 3) * (3 : ℝ) ^ h * (3 : ℝ) ^ h) ≤
        centralOrbitScale k * (n : ℝ) ^ (1 + t)) :
    centralOrbitScale k * (n : ℝ) ^ (1 - t) ≤ (orbit k n : ℝ) ∧
      (orbit k n : ℝ) ≤ centralOrbitScale k * (n : ℝ) ^ (1 + t) := by sorry
