-- Prove2me | Theorems.Thm_BitDFT_ReaderOutputStageRun_reader_outputs_stage_halt
-- name    : BitDFT.ReaderOutputStageRun.reader_outputs_stage_halt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T16:33:05.768978+00:00
-- url     : https://prove2.me/theorems/75a94d4f-114c-4250-9b3b-1452cbebbf6b
-- title:
--   Reader outputs compose with the exact coordinate operand staging run
-- statement:
--   If the Fourier reader has written a signed coordinate record and the header reader has retained the dimension, the disjoint-bank routing places both words at the exact staging tapes. Provided the dimension fits the coordinate precision, the common-host operand controller then reaches a halted configuration in exactly $2|d|+3q+14$ transitions, where $d$ is the binary dimension word and $q$ is the coordinate width. This composes the reader-frame construction with the explicit physical operand staging run.
-- source:
--   Composes the accepted reader-output host-frame theorem with the accepted coordinate-pair staging theorem. The resulting exact run is the physical handoff required before invoking the tracked multiplier.

import Definitions.Def_BitDFT_ReaderOutputStageRun
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open IntMul

theorem BitDFT.ReaderOutputStageRun.reader_outputs_stage_halt
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
      ∃ final : (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo).machine.Cfg,
        (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo).machine.step ^[
          2 * dimension.length + 3 * low.length + 14]
          (@BitDFT.ReaderOutputStageRun.entryFrame N coord dim out hc hd ho hcd hco hdo base ([sign, high] ++ low)) = final ∧
        final.state = BitDFT.OperandStage.State.halt := by sorry
