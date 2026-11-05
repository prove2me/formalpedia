-- Prove2me | Theorems.Thm_BitDFT_unpackerBin_step
-- name    : BitDFT.unpackerBin_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:10:48.303516+00:00
-- url     : https://prove2.me/theorems/7343ae12-1f09-4b9d-9f2a-475fe53bd34c
-- title:
--   One transition of the countdown: erase, step back, advance
-- statement:
--   After the unary prefix of $r$ has been counted and its counter rewound, the machine spends that count while advancing along the binary digits of $r$. The theorem records one transition of that countdown, on a mark, at the level of the two tapes it touches.
--
--   Three things happen and nothing else. The phase does not change. On the counter tape the scanned mark is erased — the head is left on a blank, which is how the count is decremented in place — and the counter head steps one cell left, towards the earlier marks. On the input tape the scanned symbol is kept and the input head steps one cell right, so the digits of $r$ are read in order, one digit charged to one mark.
--
--   Nothing is said about the other four tapes, because the phase's rule reads only the counter and input cells and the machine's guard on those tapes reads only those same cells. That is what makes the frame small enough to iterate: the countdown's progress and its recorded cells depend on the counter and the input alone.
--
--   The hypotheses are not decoration. The counter cell must hold a mark, otherwise the phase takes its exit branch; the input cell must not be the end marker, which always holds once the head has left cell $0$. The counter cell is likewise not the marker, since it holds a mark — this is the condition whose absence in the machine's earlier versions silently discarded every recorded mark.
-- source:
--   Internal: single-step frame transition for the binary-digit countdown of Prove2me's BitDFT.unpacking_machine (https://prove2.me/theorems/3a9d0791-96d8-4079-919b-de51b895da98), against the machine definition BitDFT_unpackerMachineV4.

import Definitions.Def_BitDFT_unpackerMachineV4

theorem BitDFT.unpackerBin_step (c : BitDFT.Unpacker.machine.Cfg) (ci cc : ℕ → TMKit.Sym)
    (hi hc : ℕ)
    (h1 : c.state = some ⟨BitDFT.Unpacker.Ph.rBinary, false, false, false⟩)
    (h2 : c.cells BitDFT.Unpacker.machine.inTape = ci)
    (h3 : c.head BitDFT.Unpacker.machine.inTape = hi)
    (h4 : c.cells (⟨5, by delta BitDFT.Unpacker.machine; norm_num⟩ : Fin BitDFT.Unpacker.machine.k) = cc)
    (h5 : c.head (⟨5, by delta BitDFT.Unpacker.machine; norm_num⟩ : Fin BitDFT.Unpacker.machine.k) = hc)
    (hmark : cc hc = TMKit.Sym.one) (hin : ci hi ≠ TMKit.Sym.start) :
    (BitDFT.Unpacker.machine.step c).state
        = some ⟨BitDFT.Unpacker.Ph.rBinary, false, false, false⟩ ∧
      (BitDFT.Unpacker.machine.step c).cells BitDFT.Unpacker.machine.inTape = ci ∧
      (BitDFT.Unpacker.machine.step c).head BitDFT.Unpacker.machine.inTape = hi + 1 ∧
      (BitDFT.Unpacker.machine.step c).cells
          (⟨5, by delta BitDFT.Unpacker.machine; norm_num⟩ : Fin BitDFT.Unpacker.machine.k)
        = Function.update cc hc TMKit.Sym.blank ∧
      (BitDFT.Unpacker.machine.step c).head
          (⟨5, by delta BitDFT.Unpacker.machine; norm_num⟩ : Fin BitDFT.Unpacker.machine.k)
        = hc - 1 := by sorry
