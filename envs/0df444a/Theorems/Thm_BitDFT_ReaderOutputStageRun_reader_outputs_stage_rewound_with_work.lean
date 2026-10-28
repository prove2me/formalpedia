-- Prove2me | Theorems.Thm_BitDFT_ReaderOutputStageRun_reader_outputs_stage_rewound_with_work
-- name    : BitDFT.ReaderOutputStageRun.reader_outputs_stage_rewound_with_work
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T19:03:46.555084+00:00
-- url     : https://prove2.me/theorems/d3dc796b-0a1c-4280-ac04-3e4fcc89a2d2
-- title:
--   Reader staging and output rewind preserve the multiplier work frame
-- statement:
--   When the Fourier reader has written a signed coordinate and the header reader has retained the dimension, the shared host performs the exact operand-staging run. Its output buffer contains the padded dimension and coordinate record, and the output rewind returns the head to cell one. Throughout that rewind, every dedicated multiplier work tape remains blank and its head remains at cell one.
-- source:
--   Composes the accepted reader-to-stage run with the accepted output-buffer rewind theorem and the accepted invariant that rewinding the output tape preserves all distinct multiplier work tapes.

import Definitions.Def_BitDFT_ReaderOutputStageSupport
import Definitions.Def_BitDFT_BankedOperandStage
import Definitions.Def_BitDFT_ReaderHostFrame_WorkSupport_v2
import Definitions.Def_BitDFT_RewindTape
import Theorems.Thm_BitDFT_ReaderOutputStageRun_reader_outputs_stage_halt_with_work_v2
import Theorems.Thm_BitDFT_BankedOperandStageProof_stage_halt_then_rewind
import Mathlib.Data.List.GetD
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open IntMul BitDFT.MachineSequence

theorem BitDFT.ReaderOutputStageRun.reader_outputs_stage_rewound_with_work
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
    ∃ base : (BitDFT.BankedOperandStage.controller A M H j hj).machine.Cfg,
      base.cells dim = N.tapeOf (dimension.map N.bitSym) ∧
      base.head dim = dimension.length + 1 ∧
      base.cells coord = N.tapeOf (([sign, high] ++ low).map N.bitSym) ∧
      base.head coord = low.length + 3 ∧
      (∀ i : Fin (M.k + 2), 2 ≤ i.val →
        base.cells (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) = N.tapeOf [] ∧
        base.head (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) = 1) ∧
      ∃ final : (BitDFT.BankedOperandStage.controller A M H j hj).machine.Cfg,
        (BitDFT.BankedOperandStage.controller A M H j hj).machine.step ^[
          2 * dimension.length + 3 * low.length + 14]
          (@BitDFT.ReaderOutputStageRun.entryFrame N coord dim out hc hd ho hcd hco hdo
            base ([sign, high] ++ low)) = final ∧
        final.state = BitDFT.OperandStage.State.halt ∧
        final.cells out = N.tapeOf (N.blank ::
          (List.replicate (low.length - dimension.length) N.zero ++
            dimension.map N.bitSym ++ [N.sep] ++ low.map N.bitSym)) ∧
        ∃ v ≤ final.head out + 2,
          (BitDFT.MachineSequence.sequence
            (BitDFT.BankedOperandStage.controller A M H j hj)
            (BitDFT.RewindTape.control N out)).machine.step^[v]
            (BitDFT.MachineSequence.leftCfg
              (BitDFT.BankedOperandStage.controller A M H j hj)
              (BitDFT.RewindTape.control N out) final) =
            BitDFT.MachineSequence.rightCfg
              (BitDFT.BankedOperandStage.controller A M H j hj)
              (BitDFT.RewindTape.control N out)
              (BitDFT.RewindTape.frame N out ⟨N.qStart, final.cells, final.head⟩ true 1) ∧
          ∀ i : Fin (M.k + 2), 2 ≤ i.val →
            (BitDFT.RewindTape.frame N out
              ⟨N.qStart, final.cells, final.head⟩ true 1).cells
                (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) = N.tapeOf [] ∧
            (BitDFT.RewindTape.frame N out
              ⟨N.qStart, final.cells, final.head⟩ true 1).head
                (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) = 1 := by sorry
