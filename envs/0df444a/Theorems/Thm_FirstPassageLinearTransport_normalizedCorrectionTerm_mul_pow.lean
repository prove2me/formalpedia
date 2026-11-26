-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_normalizedCorrectionTerm_mul_pow
-- name    : FirstPassageLinearTransport.normalizedCorrectionTerm_mul_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:04:10.375795+00:00
-- url     : https://prove2.me/theorems/9d4a894e-334d-5d3e-a145-2d0897237c96
-- title:
--   First Passage Linear Transport: normalized Correction Term mul pow
-- statement:
--   The First Passage Linear Transport construction uses the normalized Correction Term mul pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L103-L116
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L103-L116

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section

theorem FirstPassageLinearTransport.normalizedCorrectionTerm_mul_pow {k n i : ℕ} (hi : i < k) :
    normalizedCorrectionTerm k n i * (3 : ℝ) ^ oddCount n k =
      parityDigitR n i *
        (3 : ℝ) ^ (oddCount n k - oddCount n (i + 1)) /
          (2 : ℝ) ^ (k - i) := by sorry
