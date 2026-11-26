-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_normalizedCorrection_scaled_le_maximal
-- name    : FirstPassageLinearTransport.normalizedCorrection_scaled_le_maximal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:01:36.012024+00:00
-- url     : https://prove2.me/theorems/52b04c3f-d13c-5428-9963-b99e39ef03ce
-- title:
--   First Passage Linear Transport: normalized Correction scaled le maximal
-- statement:
--   The affine-correction estimate in the uniform form consumed downstream.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L228-L279
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L228-L279

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section

theorem FirstPassageLinearTransport.normalizedCorrection_scaled_le_maximal
    {n M k : ℕ} {h : ℝ}
    (hkM : k ≤ M)
    (hreg : MaximalParityRegular n M h) :
    normalizedCorrection k n * (3 : ℝ) ^ ((k : ℝ) / 2) ≤
      (2 + Real.sqrt 3) * (3 : ℝ) ^ h := by sorry
