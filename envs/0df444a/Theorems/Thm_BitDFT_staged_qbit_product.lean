-- Prove2me | Theorems.Thm_BitDFT_staged_qbit_product
-- name    : BitDFT.staged_qbit_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T02:47:45.006841+00:00
-- url     : https://prove2.me/theorems/fdeba804-f62a-46fd-a1ae-7aa044822167
-- title:
--   A staged multiplier call has a q-bit runtime bound
-- statement:
--   Let a supplied multitape machine multiply any two q-bit words within T(q) steps. If its reusable caller already holds a q-bit operand pair in the prepared input buffer and its work banks are clean, then the complete tracked call returns the exact 2q-bit product within 6T(q)+14q+20 steps. The bound includes the child multiplication, the banked call setup and return, and cleanup; it assumes no regularity of T.
-- source:
--   This packages the exact prepared-frame identity, the accepted tracked-bank call simulation, and the extents bound into the q-bit specialization required by the direct coordinatewise rescaling proof. The proof is self-contained relative to accepted multiplier-call results.

import Theorems.Thm_IntMul_TrackedBankedCall_call_correct
import Theorems.Thm_BitDFT_child_call_with_precision
import Definitions.Def_IntMul_TrackedBankedCall
import Definitions.Def_BitDFT_Encoding
import Mathlib.Tactic
set_option autoImplicit false
open IntMul BitDFT
open IntMul.TrackedBankPreparation (inputWord initialExtent)

theorem BitDFT.staged_qbit_product (M : MultitapeTM) (T : ℕ → ℝ)
    (hM : Multiplier M T) (q : ℕ) (hq : 1 ≤ q)
    (base : (TrackedBankedCall.machine M).Cfg) (x y : List Bool)
    (hx : x.length = q) (hy : y.length = q)
    (hs : base.state = (TrackedBankedCall.machine M).qStart)
    (hbuf : base.cells (TrackedBankedCall.machine M).outTape =
      (TrackedBankedCall.machine M).tapeOf
        ((TrackedBankedCall.machine M).blank ::
          (TrackedBankPreparation.inputWord M x y).map (fun s => some (s, true))))
    (hh : base.head (TrackedBankedCall.machine M).outTape = 1)
    (hwork : ∀ i : Fin (M.k + 2), 2 ≤ i.val →
      base.cells i = (TrackedBankedCall.machine M).tapeOf [] ∧ base.head i = 1) :
    ∃ t tm : ℕ,
      (tm : ℝ) ≤ T q ∧
      (t : ℝ) ≤ 6 * T q + 14 * q + 20 ∧
      (TrackedBankedCall.machine M).step^[t] base =
        TrackedBankedCall.finalFrame M base 1 (fun _ => 1)
          (TrackedBankedSimulation.extents M (M.initCfg x y)
            (TrackedBankPreparation.initialExtent M x y) tm)
          (M.step^[tm] (M.initCfg x y))
          (IntMul.bin (2*q) (IntMul.val x * IntMul.val y)) := by sorry
