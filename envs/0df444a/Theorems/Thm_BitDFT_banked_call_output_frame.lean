-- Prove2me | Theorems.Thm_BitDFT_banked_call_output_frame
-- name    : BitDFT.banked_call_output_frame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T03:57:27.588165+00:00
-- url     : https://prove2.me/theorems/249c827a-f73d-46d3-a22a-d6311e7846ac
-- title:
--   The reusable multiplier exposes its exact tagged output frame
-- statement:
--   Let a reusable multiplier caller reserve a buffer prefix of length σ and return the binary word w. In the final caller frame, the output tape contains the j-th symbol of w at position σ+j+1, tagged as visited exactly when j<|w|; positions beyond the payload decode as blank. The output head is at σ+|w|+1. This gives the exact physical output frame needed to pass a multiplier result into the following serialization stage.
-- source:
--   Exact output-tape invariant for the tracked reusable multiplier caller, derived from its physical return buffer and cleanup frames. This supplies the multiplier-to-serializer tape-layout interface; it does not claim the full vector scaler is assembled.

import Definitions.Def_IntMul_TrackedBankedCall
set_option autoImplicit false
open IntMul

theorem BitDFT.banked_call_output_frame (M : IntMul.MultitapeTM)
    (base : (IntMul.TrackedBankedCall.machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (j : ℕ) :
    (IntMul.TrackedBankedCall.finalFrame M base sigma offset extent c w).cells
      (IntMul.TrackedBankedCall.machine M).outTape (sigma + j + 1) =
        some ((w.map M.bitSym).getD j M.blank, decide (j < w.length)) ∧
    (IntMul.TrackedBankedCall.finalFrame M base sigma offset extent c w).head
      (IntMul.TrackedBankedCall.machine M).outTape = sigma + w.length + 1 := by sorry
