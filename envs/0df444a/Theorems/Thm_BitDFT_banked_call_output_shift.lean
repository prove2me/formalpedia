-- Prove2me | Theorems.Thm_BitDFT_banked_call_output_shift
-- name    : BitDFT.banked_call_output_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T04:06:39.637056+00:00
-- url     : https://prove2.me/theorems/f2fca413-6ed6-4baf-ada9-422a42a58885
-- title:
--   Run output normalization immediately after a multiplier call
-- statement:
--   After a reusable multiplier call returns a word w, the fixed output-normalization controller runs from the exact returned configuration to its normalized output frame. The normalization takes 4|w|+4 transitions and produces a canonical output word while preserving the caller’s other tape data.
-- source:
--   Composition of the accepted multiplier-to-normalizer handoff frame with the fixed output-shift execution theorem. This is the actual normalization run following a coordinate multiplier call.

import Definitions.Def_IntMul_TrackedBankedCall
import Definitions.Def_IntMul_TrackedOutputShift
import Theorems.Thm_IntMul_TrackedOutputShift_shift_correct
import Theorems.Thm_BitDFT_banked_call_shift_handoff
set_option autoImplicit false
open IntMul

theorem BitDFT.banked_call_output_shift (M : IntMul.MultitapeTM)
    (base : (IntMul.TrackedBankedCall.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) :
    (IntMul.TrackedOutputShift.machine M).step^[4 * w.length + 4]
      (⟨.rewind,
        (IntMul.TrackedBankedCall.finalFrame M base 1 offset extent c w).cells,
        (IntMul.TrackedBankedCall.finalFrame M base 1 offset extent c w).head⟩ :
        (IntMul.TrackedOutputShift.machine M).Cfg) =
    IntMul.TrackedOutputShift.finalFrame M
      (⟨.rewind,
        (IntMul.TrackedBankedCall.finalFrame M base 1 offset extent c w).cells,
        (IntMul.TrackedBankedCall.finalFrame M base 1 offset extent c w).head⟩ :
        (IntMul.TrackedOutputShift.machine M).Cfg) w := by sorry
