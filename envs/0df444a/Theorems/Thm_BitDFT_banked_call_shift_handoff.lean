-- Prove2me | Theorems.Thm_BitDFT_banked_call_shift_handoff
-- name    : BitDFT.banked_call_shift_handoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T04:04:27.806367+00:00
-- url     : https://prove2.me/theorems/69a6c466-bece-4e2e-89c8-f787f29bc593
-- title:
--   A returned product is ready for output normalization
-- statement:
--   After a tracked multiplier call has returned the word w to its caller buffer, changing only the control state to the output-normalization phase yields exactly that phase’s prescribed rewind frame. In particular, the call leaves the payload and its head at the positions expected by the output-shift routine, so the following normalization run begins immediately from the returned configuration.
-- source:
--   Frame-level composition of the accepted tracked-call output invariant and the output-shift controller. This is the exact multiplier-to-normalizer handoff used before serialization.

import Definitions.Def_IntMul_TrackedBankedCall
import Definitions.Def_IntMul_TrackedOutputShift
import Theorems.Thm_BitDFT_banked_call_output_frame
set_option autoImplicit false
open IntMul

theorem BitDFT.banked_call_shift_handoff (M : IntMul.MultitapeTM)
    (base : (IntMul.TrackedBankedCall.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) :
    IntMul.TrackedOutputShift.rewindFrame M
      (⟨.rewind,
        (IntMul.TrackedBankedCall.finalFrame M base 1 offset extent c w).cells,
        (IntMul.TrackedBankedCall.finalFrame M base 1 offset extent c w).head⟩ :
        (IntMul.TrackedOutputShift.machine M).Cfg)
      w (w.length + 2) =
    (⟨.rewind,
      (IntMul.TrackedBankedCall.finalFrame M base 1 offset extent c w).cells,
      (IntMul.TrackedBankedCall.finalFrame M base 1 offset extent c w).head⟩ :
      (IntMul.TrackedOutputShift.machine M).Cfg) := by sorry
