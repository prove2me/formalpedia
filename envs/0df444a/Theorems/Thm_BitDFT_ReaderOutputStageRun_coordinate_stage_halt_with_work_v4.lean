-- Prove2me | Theorems.Thm_BitDFT_ReaderOutputStageRun_coordinate_stage_halt_with_work_v4
-- name    : BitDFT.ReaderOutputStageRun.coordinate_stage_halt_with_work_v4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T18:12:40.024741+00:00
-- url     : https://prove2.me/theorems/0140a543-ffd0-4900-a01e-d90f4e5338ed
-- title:
--   Coordinate staging preserves a clean multiplier work bank (v4)
-- statement:
--   Assume the operand staging controller begins with the encoded dimension and signed coordinate and that all tracked multiplier work tapes are blank with their heads at cell 1. Then it halts after the exact prescribed run, writes the padded dimension and coordinate in the output buffer, and preserves those work tapes.
-- source:
--   Composes the accepted exact coordinate-pair run, output-buffer result, and frame-preservation invariant. The explicit clean-work-bank premise is discharged by the reader-frame theorem.

import Definitions.Def_BitDFT_BankedOperandStageProofSupport
import Definitions.Def_BitDFT_OperandStage
import Definitions.Def_BitDFT_ReaderOutputStageSupport
import Theorems.Thm_BitDFT_OperandStage_run_preserves_other_tape
import Theorems.Thm_BitDFT_BankedOperandStageProof_coordinate_pair_to_halt
import Theorems.Thm_BitDFT_BankedOperandStageProof_coordinate_pair_output_buffer
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open IntMul BitDFT.OperandStage BitDFT.MachineSequence
namespace BitDFT.ReaderOutputStageRun

theorem coordinate_stage_halt_with_work_v4
    (A M H : MultitapeTM) (j : Fin A.k)
    (dimension low : List Bool) (sign high : Bool)
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
    (base : (BitDFT.OperandStage.control (BitDFT.ReaderHostFrame.host A M H)
      (BitDFT.BankedOperandStage.coordinateTape A M H j)
      (BitDFT.BankedOperandStage.dimensionTape A M H)
      (BitDFT.BankedOperandStage.multiplierOutputTape A M H) hc hd ho hcd hco hdo).machine.Cfg)
    (hdCells : base.cells (BitDFT.BankedOperandStage.dimensionTape A M H) =
      (BitDFT.ReaderHostFrame.host A M H).tapeOf
        (dimension.map (BitDFT.ReaderHostFrame.host A M H).bitSym))
    (hdHead : base.head (BitDFT.BankedOperandStage.dimensionTape A M H) = dimension.length + 1)
    (hcCells : base.cells (BitDFT.BankedOperandStage.coordinateTape A M H j) =
      (BitDFT.ReaderHostFrame.host A M H).tapeOf
        (([sign, high] ++ low).map (BitDFT.ReaderHostFrame.host A M H).bitSym))
    (hcHead : base.head (BitDFT.BankedOperandStage.coordinateTape A M H j) = low.length + 3)
    (hworkBase : ∀ i : Fin (M.k + 2), 2 ≤ i.val →
      base.cells (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) =
        (BitDFT.ReaderHostFrame.host A M H).tapeOf [] ∧
      base.head (BitDFT.ReaderHostFrame.multiplierTapeRoute A M H i) = 1)
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
