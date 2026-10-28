-- Prove2me | Theorems.Thm_BitDFT_staged_call_run
-- name    : BitDFT.staged_call_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T02:39:12.577341+00:00
-- url     : https://prove2.me/theorems/c868fc3c-7919-45ad-8405-3d877de56ee7
-- title:
--   Run a reusable multiplier from an already staged operand buffer
-- statement:
--   Suppose a caller has already placed two binary operands in the tracked multiplier caller’s mutable buffer, with its work banks blank and its heads prepared. Then the setup phase is an exact identity on that caller frame. If the multiplier halts on the staged operands after T steps with output w, the reusable banked-call machine runs from that same frame to its fully cleaned final frame, with the child execution, output return, and cleanup all included in the stated time bound.
-- source:
--   Concrete reuse interface for the coordinatewise output-rescaling stage. It combines the exact staged-buffer frame identity with the accepted tracked-bank call simulation; it does not assume that operands can be staged for free.

import Definitions.Def_IntMul_TrackedBankedCall
import Theorems.Thm_IntMul_TrackedBankedCall_call_correct
import Theorems.Thm_BitDFT_child_call_with_precision
set_option autoImplicit false
open IntMul

theorem BitDFT.staged_call_run (M : MultitapeTM)
    (base : (TrackedBankedCall.machine M).Cfg) (x y : List Bool)
    (hs : base.state = (TrackedBankedCall.machine M).qStart)
    (hbuf : base.cells (TrackedBankedCall.machine M).outTape =
      (TrackedBankedCall.machine M).tapeOf
        ((TrackedBankedCall.machine M).blank ::
          (TrackedBankPreparation.inputWord M x y).map
            (fun s => some (s, true))))
    (hh : base.head (TrackedBankedCall.machine M).outTape = 1)
    (hwork : ∀ i : Fin (M.k + 2), 2 ≤ i.val →
      base.cells i = (TrackedBankedCall.machine M).tapeOf [] ∧ base.head i = 1)
    (T : ℕ) (halt : (M.step^[T] (M.initCfg x y)).state = M.qHalt)
    (w : List Bool)
    (hout : (M.step^[T] (M.initCfg x y)).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    ∃ t : ℕ, t ≤ T + 5 * IntMul.TrackedBankCleanup.span M
        (IntMul.TrackedBankedSimulation.extents M (M.initCfg x y)
          (IntMul.TrackedBankPreparation.initialExtent M x y) T) +
        2 * (IntMul.TrackedBankPreparation.inputWord M x y).length + 13 ∧
      (TrackedBankedCall.machine M).step^[t] base =
        TrackedBankedCall.finalFrame M base 1 (fun _ => 1)
          (IntMul.TrackedBankedSimulation.extents M (M.initCfg x y)
            (IntMul.TrackedBankPreparation.initialExtent M x y) T)
          (M.step^[T] (M.initCfg x y)) w := by sorry
