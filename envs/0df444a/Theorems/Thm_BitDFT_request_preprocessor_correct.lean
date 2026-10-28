-- Prove2me | Theorems.Thm_BitDFT_request_preprocessor_correct
-- name    : BitDFT.request_preprocessor_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:41:27.044995+00:00
-- url     : https://prove2.me/theorems/308950a5-7713-4fa4-8fa9-4e2fa11de55f
-- title:
--   Construct the guarded Fourier input in at most 27nq actual transitions
-- statement:
--   For every n,b≥1 and every integer-pair vector U of length n, set q=b+3 max(ceil(log₂ n),1)+5. The fixed machine RewriteInput computes exactly fourierInput(q,U) from requestedInput(b,U) within 27nq transitions. This is the mission’s full native binary input/output contract, including halting and the exact blank tail of the output tape. No unit-disc assumption is needed for this encoding conversion.
-- source:
--   Specializes the complete native-input rewriting machine to the mission’s vector representation. This closes the input-conversion stage of the rescaling wrapper, while leaving arbitrary-A simulation and multiplier-backed output scaling unproved.

import Definitions.Def_BitDFT_RewriteInput
open BitDFT IntMul

theorem BitDFT.request_preprocessor_correct (n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) (U : Fin n → ℤ × ℤ) :
    Computes RewriteInput.machine (requestedInput b U) (fourierInput (guardPrecision n b) U)
      (27 * (n : ℝ) * (guardPrecision n b : ℝ)) := by sorry
