-- Prove2me | Theorems.Thm_BitDFT_ReaderHostFrame_reader_stage_reaches_multiplier_call
-- name    : BitDFT.ReaderHostFrame.reader_stage_reaches_multiplier_call
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T19:43:06.697199+00:00
-- url     : https://prove2.me/theorems/80e74cec-5549-4f33-9d46-0fdfa25e0741
-- title:
--   The rewound reader output starts the tracked multiplier call
-- statement:
--   Given an input frame for the coordinate and dimension reader, the accepted reader-to-staging theorem rewinds the staged multiplier buffer to cell one and leaves the multiplier work tapes blank. Projecting that host frame through the multiplier alphabet embedding yields the tracked caller configuration. Therefore the tracked multiplication call can begin on the padded dimension and coordinate operands, with its proved execution bound.
-- source:
--   Composes the accepted reader-output staging/rewind frame theorem with the exact host-buffer projection and staged-call runtime theorem. The dimension is left-padded to the coordinate width before multiplication.

import Definitions.Def_BitDFT_ReaderHostFrame_WorkSupport_v2
import Theorems.Thm_BitDFT_ReaderOutputStageRun_reader_outputs_stage_rewound_with_work
import Theorems.Thm_BitDFT_staged_call_from_host_buffer
import Theorems.Thm_BitDFT_ReaderHostFrame_staging_output_route_is_tracked_output
import Theorems.Thm_BitDFT_ReaderHostFrame_tracked_input_word_embeds
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open IntMul BitDFT

theorem BitDFT.ReaderHostFrame.reader_stage_reaches_multiplier_call
    (A M H : MultitapeTM) (hH4 : 3 < H.k)
    (cF : A.Cfg) (cH : H.Cfg) (j : Fin A.k) (hj : 1 ≤ j.val)
    (dimension low : List Bool) (sign high : Bool)
    (hcoord : cF.cells j = A.tapeOf (([sign, high] ++ low).map A.bitSym))
    (hdim : cH.cells ⟨3, hH4⟩ = H.tapeOf (dimension.map H.bitSym))
    (hdimHead : cH.head ⟨3, hH4⟩ = dimension.length + 1)
    (hq : dimension.length ≤ low.length)
    (hc : BankedOperandStage.coordinateTape A M H j ≠ (host A M H).inTape)
    (hd : BankedOperandStage.dimensionTape A M H ≠ (host A M H).inTape)
    (ho : BankedOperandStage.multiplierOutputTape A M H ≠ (host A M H).inTape)
    (hcd : BankedOperandStage.coordinateTape A M H j ≠ BankedOperandStage.dimensionTape A M H)
    (hco : BankedOperandStage.coordinateTape A M H j ≠ BankedOperandStage.multiplierOutputTape A M H)
    (hdo : BankedOperandStage.dimensionTape A M H ≠ BankedOperandStage.multiplierOutputTape A M H)
    (hpad : ∀ p, 1 ≤ p →
      ((host A M H).tapeOf ((host A M H).blank ::
        List.replicate low.length (host A M H).zero)) p ≠ (host A M H).startSym)
    (hdimBlank : ((host A M H).tapeOf (dimension.map (host A M H).bitSym))
        (dimension.length + 1) = (host A M H).blank)
    (T : ℕ) (halt : (M.step^[T] (M.initCfg
        (List.replicate (low.length - dimension.length) false ++ dimension) low)).state = M.qHalt)
    (w : List Bool)
    (hout : (M.step^[T] (M.initCfg
        (List.replicate (low.length - dimension.length) false ++ dimension) low)).cells M.outTape =
          M.tapeOf (w.map M.bitSym)) :
    ∃ base : (TrackedBankedCall.machine M).Cfg, ∃ t : ℕ,
      base.state = (TrackedBankedCall.machine M).qStart ∧
      base.cells (TrackedBankedCall.machine M).outTape =
        (TrackedBankedCall.machine M).tapeOf
          ((TrackedBankedCall.machine M).blank ::
            (TrackedBankPreparation.inputWord M
              (List.replicate (low.length - dimension.length) false ++ dimension) low).map
              (fun s => some (s, true))) ∧
      base.head (TrackedBankedCall.machine M).outTape = 1 ∧
      (∀ i : Fin (M.k + 2), 2 ≤ i.val →
        base.cells i = (TrackedBankedCall.machine M).tapeOf [] ∧ base.head i = 1) ∧
      ∃ t' : ℕ,
        t' ≤ T + 5 * TrackedBankCleanup.span M
          (TrackedBankedSimulation.extents M
            (M.initCfg (List.replicate (low.length - dimension.length) false ++ dimension) low)
            (TrackedBankPreparation.initialExtent M
              (List.replicate (low.length - dimension.length) false ++ dimension) low) T) +
          2 * (TrackedBankPreparation.inputWord M
            (List.replicate (low.length - dimension.length) false ++ dimension) low).length + 13 ∧
        (TrackedBankedCall.machine M).step^[t'] base =
          TrackedBankedCall.finalFrame M base 1 (fun _ => 1)
            (TrackedBankedSimulation.extents M
              (M.initCfg (List.replicate (low.length - dimension.length) false ++ dimension) low)
              (TrackedBankPreparation.initialExtent M
                (List.replicate (low.length - dimension.length) false ++ dimension) low) T)
            (M.step^[T] (M.initCfg
              (List.replicate (low.length - dimension.length) false ++ dimension) low)) w := by sorry
