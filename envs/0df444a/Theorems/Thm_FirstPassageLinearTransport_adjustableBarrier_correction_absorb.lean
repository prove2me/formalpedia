-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_adjustableBarrier_correction_absorb
-- name    : FirstPassageLinearTransport.adjustableBarrier_correction_absorb
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:13:11.57271+00:00
-- url     : https://prove2.me/theorems/54961e58-a4c0-5db4-8cb1-15d3fb891678
-- title:
--   First Passage Linear Transport: adjustable Barrier correction absorb
-- statement:
--   The affine correction is absorbed once its fixed constant fits in the
--   unused exponent `a0 + t - 2 * lambda * t`.  This is the exact finite-startup
--   condition needed by the adjustable barrier; eventuality is kept separate.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AdjustableEnvelope.lean#L138-L196
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/AdjustableEnvelope.lean#L138-L196

import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_AdjustableEnvelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.adjustableBarrier_correction_absorb
    {lambda t : ℝ} {M n k : ℕ}
    (ht : 0 ≤ t) (hkM : k ≤ M) (hnShell : n ∈ dyadicShell M)
    (hstartup :
      2 * (2 + Real.sqrt 3) ≤
        (2 : ℝ) ^ ((a0 + t - 2 * lambda * t) * (M : ℝ))) :
    2 * ((2 + Real.sqrt 3) *
        (3 : ℝ) ^ adjustableBarrierHeight lambda t M *
        (3 : ℝ) ^ adjustableBarrierHeight lambda t M) ≤
      centralOrbitScale k * (n : ℝ) ^ (1 + t) := by sorry
