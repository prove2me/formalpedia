-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_normalizedCorrectionTerm_scaled_le_maximal
-- name    : FirstPassageLinearTransport.normalizedCorrectionTerm_scaled_le_maximal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:05:27.787015+00:00
-- url     : https://prove2.me/theorems/5f255e6f-6e30-506c-a0fd-5b5a538525ea
-- title:
--   First Passage Linear Transport: normalized Correction Term scaled le maximal
-- statement:
--   A single normalized correction term is bounded by one term of the fixed
--   geometric series with ratio `rho`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L156-L225
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L156-L225

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section

theorem FirstPassageLinearTransport.normalizedCorrectionTerm_scaled_le_maximal
    {n M k i : ℕ} {h : ℝ}
    (hik : i < k) (hkM : k ≤ M)
    (hreg : MaximalParityRegular n M h) :
    normalizedCorrectionTerm k n i * (3 : ℝ) ^ ((k : ℝ) / 2) ≤
      (3 : ℝ) ^ h / 2 * rho ^ (k - 1 - i) := by sorry
