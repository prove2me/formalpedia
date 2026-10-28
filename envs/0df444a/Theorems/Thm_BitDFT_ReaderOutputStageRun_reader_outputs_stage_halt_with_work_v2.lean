-- Prove2me | Theorems.Thm_BitDFT_ReaderOutputStageRun_reader_outputs_stage_halt_with_work_v2
-- name    : BitDFT.ReaderOutputStageRun.reader_outputs_stage_halt_with_work_v2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T18:17:33.351499+00:00
-- url     : https://prove2.me/theorems/f9477012-a38f-47d2-8388-753592156639
-- title:
--   Reader staging halts with the multiplier work bank intact
-- statement:
--   When the Fourier-coordinate reader and header parser leave their encoded words in the common host, the operand-staging controller reaches its exact halt state and writes the padded dimension, separator, and signed coordinate in the multiplier buffer. The staged run also leaves every tracked multiplier work tape blank with its head at cell 1.
-- source:
--   Composes the accepted reader-frame work-bank theorem with the exact coordinate-pair staging run, output-buffer theorem, and accepted frame invariant. This supplies the complete initial multiplier-call interface.

import Definitions.Def_BitDFT_BankedOperandStageProofSupport
import Definitions.Def_BitDFT_OperandStage
import Definitions.Def_BitDFT_ReaderHostFrame_WorkSupport_v2
import Definitions.Def_BitDFT_ReaderOutputStageSupport
import Theorems.Thm_BitDFT_ReaderHostFrame_reader_outputs_to_operand_frame_with_work_v3
import Theorems.Thm_BitDFT_OperandStage_run_preserves_other_tape
import Theorems.Thm_BitDFT_BankedOperandStageProof_coordinate_pair_to_halt
import Theorems.Thm_BitDFT_BankedOperandStageProof_coordinate_pair_output_buffer
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open IntMul BitDFT.OperandStage BitDFT.MachineSequence
namespace BitDFT.ReaderOutputStageRun

theorem reader_outputs_stage_halt_with_work_v2
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
      (∀ i : Fin (M.k + 2), 2 ≤ i.val →
        base.cells (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) = N.tapeOf [] ∧
        base.head (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) = 1) ∧
      ∃ final : (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo).machine.Cfg,
        (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo).machine.step ^[
          2 * dimension.length + 3 * low.length + 14]
          (@BitDFT.ReaderOutputStageRun.entryFrame N coord dim out hc hd ho hcd hco hdo base
            ([sign, high] ++ low)) = final ∧
        final.state = BitDFT.OperandStage.State.halt ∧
        final.cells out = N.tapeOf (N.blank ::
          (List.replicate (low.length - dimension.length) N.zero ++
            dimension.map N.bitSym ++ [N.sep] ++ low.map N.bitSym)) ∧
        (∀ i : Fin (M.k + 2), 2 ≤ i.val →
          final.cells (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) = N.tapeOf [] ∧
          final.head (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) = 1) := by sorry
