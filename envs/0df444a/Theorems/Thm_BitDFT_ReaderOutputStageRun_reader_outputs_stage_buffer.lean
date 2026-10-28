-- Prove2me | Theorems.Thm_BitDFT_ReaderOutputStageRun_reader_outputs_stage_buffer
-- name    : BitDFT.ReaderOutputStageRun.reader_outputs_stage_buffer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T16:47:46.325396+00:00
-- url     : https://prove2.me/theorems/55a83df5-e1c6-4491-891c-9129bd1ef797
-- title:
--   Actual reader outputs yield the exact multiplier operand buffer
-- statement:
--   For a parsed dimension and a signed q-bit coordinate present in the disjoint reader banks, the common host stage constructs a base frame and leaves the caller buffer exactly as a blank sentinel followed by the padded dimension bits, separator, and coordinate bits. This is the concrete operand-pair tape layout used by the tracked multiplier.
-- source:
--   Composes the accepted reader-output host-frame theorem with the accepted cell-level operand-staging output theorem.

import Definitions.Def_BitDFT_ReaderOutputStageRun
import Theorems.Thm_BitDFT_BankedOperandStageProof_coordinate_pair_output_buffer
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open IntMul BitDFT.OperandStage
namespace BitDFT.ReaderOutputStageRun

theorem reader_outputs_stage_buffer
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
      ((BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo).machine.step ^[
        2 * dimension.length + 3 * low.length + 14]
        (@BitDFT.ReaderOutputStageRun.entryFrame N coord dim out hc hd ho hcd hco hdo base
          ([sign, high] ++ low))).cells out =
        N.tapeOf (N.blank ::
          (List.replicate (low.length - dimension.length) N.zero ++
            dimension.map N.bitSym ++ [N.sep] ++ low.map N.bitSym)) := by sorry
