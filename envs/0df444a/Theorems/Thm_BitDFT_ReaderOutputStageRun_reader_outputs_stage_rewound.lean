-- Prove2me | Theorems.Thm_BitDFT_ReaderOutputStageRun_reader_outputs_stage_rewound
-- name    : BitDFT.ReaderOutputStageRun.reader_outputs_stage_rewound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T17:06:13.508589+00:00
-- url     : https://prove2.me/theorems/98134338-34e3-445c-8e9e-b3d77b42f2a5
-- title:
--   Reader-produced operands are rewound for a tracked multiplier call
-- statement:
--   Starting from the actual Fourier-coordinate and parsed-dimension reader tapes, stage the exact padded operand pair, halt, and rewind the multiplier input buffer to cell 1. The operand payload is preserved, so the resulting controller frame is ready for the tracked multiplier call.
-- source:
--   Composes the accepted reader-to-operand frame, exact staging halt and buffer theorems, and marker rewind correctness.

import Definitions.Def_BitDFT_ReaderOutputStageRun
import Definitions.Def_BitDFT_RewindTape
import Theorems.Thm_BitDFT_ReaderHostFrame_reader_outputs_to_operand_frame
import Theorems.Thm_BitDFT_BankedOperandStageProof_coordinate_pair_to_halt
import Theorems.Thm_BitDFT_BankedOperandStageProof_coordinate_pair_output_buffer
import Theorems.Thm_BitDFT_rewind_tape_correct
import Theorems.Thm_BitDFT_machine_sequence_bound
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open IntMul BitDFT.OperandStage BitDFT.MachineSequence
namespace BitDFT.ReaderOutputStageRun

theorem reader_outputs_stage_rewound
    (A M H : MultitapeTM) (hH4 : 3 < H.k)
    (cF : A.Cfg) (cH : H.Cfg) (j : Fin A.k) (hj : 1 ≤ j.val)
    (dimension low : List Bool) (sign high : Bool)
    (hcoord : cF.cells j = A.tapeOf (([sign, high] ++ low).map A.bitSym))
    (hdim : cH.cells ⟨3, hH4⟩ = H.tapeOf (dimension.map H.bitSym))
    (hdimHead : cH.head ⟨3, hH4⟩ = dimension.length + 1)
    (hq : dimension.length ≤ low.length)
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
    (hpad : ∀ p, 1 ≤ p →
      ((BitDFT.ReaderHostFrame.host A M H).tapeOf
        ((BitDFT.ReaderHostFrame.host A M H).blank ::
          List.replicate low.length (BitDFT.ReaderHostFrame.host A M H).zero)) p ≠
          (BitDFT.ReaderHostFrame.host A M H).startSym)
    (hdimBlank : ((BitDFT.ReaderHostFrame.host A M H).tapeOf
      (dimension.map (BitDFT.ReaderHostFrame.host A M H).bitSym))
        (dimension.length + 1) = (BitDFT.ReaderHostFrame.host A M H).blank) :
    let N := BitDFT.ReaderHostFrame.host A M H
    let coord := BitDFT.BankedOperandStage.coordinateTape A M H j
    let dim := BitDFT.BankedOperandStage.dimensionTape A M H
    let out := BitDFT.BankedOperandStage.multiplierOutputTape A M H
    ∃ base : (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo).machine.Cfg,
      base.cells dim = N.tapeOf (dimension.map N.bitSym) ∧
      base.head dim = dimension.length + 1 ∧
      base.cells coord = N.tapeOf (([sign, high] ++ low).map N.bitSym) ∧
      base.head coord = low.length + 3 ∧
      ∃ final : (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo).machine.Cfg,
        (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo).machine.step ^[
          2 * dimension.length + 3 * low.length + 14]
          (@entryFrame N coord dim out hc hd ho hcd hco hdo base ([sign, high] ++ low)) = final ∧
        final.state = BitDFT.OperandStage.State.halt ∧
        final.cells out = N.tapeOf (N.blank ::
          (List.replicate (low.length - dimension.length) N.zero ++
            dimension.map N.bitSym ++ [N.sep] ++ low.map N.bitSym)) ∧
        ∃ v ≤ final.head out + 2,
          (MachineSequence.sequence
            (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo)
            (BitDFT.RewindTape.control N out)).machine.step^[v]
            (MachineSequence.leftCfg
              (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo)
              (BitDFT.RewindTape.control N out) final) =
            MachineSequence.rightCfg
              (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo)
              (BitDFT.RewindTape.control N out)
              (BitDFT.RewindTape.frame N out
                ⟨N.qStart, final.cells, final.head⟩ true 1) := by sorry
