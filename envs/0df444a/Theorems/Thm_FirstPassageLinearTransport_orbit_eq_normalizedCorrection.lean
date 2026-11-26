-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_orbit_eq_normalizedCorrection
-- name    : FirstPassageLinearTransport.orbit_eq_normalizedCorrection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:01:03.647012+00:00
-- url     : https://prove2.me/theorems/3742b94f-f73b-5440-b991-e4649eefa706
-- title:
--   First Passage Linear Transport: orbit eq normalized Correction
-- statement:
--   V2 exact affine iterate in the normalized correction coordinate used by
--   the paper.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L120-L145
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L120-L145

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section

theorem FirstPassageLinearTransport.orbit_eq_normalizedCorrection (k n : ℕ) :
    (orbit k n : ℝ) =
      ((n : ℝ) / (2 : ℝ) ^ k + normalizedCorrection k n) *
        (3 : ℝ) ^ oddCount n k := by sorry
