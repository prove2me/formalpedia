-- Prove2me | Theorems.Thm_BitDFT_BankedOperandStageProof_stage_halt_then_rewind_preserves_work
-- name    : BitDFT.BankedOperandStageProof.stage_halt_then_rewind_preserves_work
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T18:51:37.159991+00:00
-- url     : https://prove2.me/theorems/3742f5f1-b4ec-471c-9988-a0ebf28c1e84
-- title:
--   Marker rewind preserves the staged multiplier work-bank frame
-- statement:
--   Suppose the operand-staging controller has halted with a marked output tape and every tracked multiplier work tape blank at cell zero with its head at cell one. The marker-rewind controller returns the output head to cell one in at most the original output-head position plus two steps. Because the multiplier work tapes occupy different routed addresses, rewind leaves every work tape and work head unchanged. This preserves the exact reusable-call precondition.
-- source:
--   The proof composes the accepted staging-to-rewind execution theorem with the physical multiplier-bank address formula and the exact rewind-frame definition.

import Definitions.Def_BitDFT_ReaderHostFrame_WorkSupport_v2
import Definitions.Def_BitDFT_BankedOperandStage
import Definitions.Def_BitDFT_RewindTape
import Theorems.Thm_BitDFT_BankedOperandStageProof_stage_halt_then_rewind
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open IntMul BitDFT.MachineSequence

theorem BitDFT.BankedOperandStageProof.stage_halt_then_rewind_preserves_work
    (A M H : MultitapeTM) (j : Fin A.k) (hj : 1 ≤ j.val)
    (hc : BitDFT.BankedOperandStage.coordinateTape A M H j ≠
      (BitDFT.ReaderHostFrame.host A M H).inTape)
    (hd : BitDFT.BankedOperandStage.dimensionTape A M H ≠
      (BitDFT.ReaderHostFrame.host A M H).inTape)
    (ho : BitDFT.BankedOperandStage.multiplierOutputTape A M H ≠
      (BitDFT.ReaderHostFrame.host A M H).inTape)
    (hcd : BitDFT.BankedOperandStage.coordinateTape A M H j ≠
      BitDFT.BankedOperandStage.dimensionTape A M H)
    (hco : BitDFT.BankedOperandStage.coordinateTape A M H j ≠
      BitDFT.BankedOperandStage.multiplierOutputTape A M H)
    (hdo : BitDFT.BankedOperandStage.dimensionTape A M H ≠
      BitDFT.BankedOperandStage.multiplierOutputTape A M H)
    (c : (BitDFT.BankedOperandStage.controller A M H j hj).machine.Cfg)
    (hs : c.state = BitDFT.OperandStage.State.halt)
    (p : ℕ) (hp : c.head (BitDFT.BankedOperandStage.multiplierOutputTape A M H) = p)
    (hmarker : c.cells (BitDFT.BankedOperandStage.multiplierOutputTape A M H) 0 =
      (BitDFT.ReaderHostFrame.host A M H).startSym)
    (hnomarker : ∀ i, 0 < i →
      c.cells (BitDFT.BankedOperandStage.multiplierOutputTape A M H) i ≠
        (BitDFT.ReaderHostFrame.host A M H).startSym)
    (hwork : ∀ i : Fin (M.k + 2), 2 ≤ i.val →
      c.cells (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) =
        (BitDFT.ReaderHostFrame.host A M H).tapeOf [] ∧
      c.head (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) = 1) :
    let N := BitDFT.ReaderHostFrame.host A M H
    let out := BitDFT.BankedOperandStage.multiplierOutputTape A M H
    let P := BitDFT.BankedOperandStage.controller A M H j hj
    let Q := BitDFT.RewindTape.control N out
    let rf := BitDFT.RewindTape.frame N out ⟨N.qStart, c.cells, c.head⟩ true 1
    ∃ v ≤ p + 2,
      (BitDFT.MachineSequence.sequence P Q).machine.step^[v]
        (BitDFT.MachineSequence.leftCfg P Q c) = BitDFT.MachineSequence.rightCfg P Q rf ∧
      ∀ i : Fin (M.k + 2), 2 ≤ i.val →
        rf.cells (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) = N.tapeOf [] ∧
        rf.head (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) = 1  := by sorry
