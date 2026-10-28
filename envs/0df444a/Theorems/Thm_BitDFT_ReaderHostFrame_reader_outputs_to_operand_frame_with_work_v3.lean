-- Prove2me | Theorems.Thm_BitDFT_ReaderHostFrame_reader_outputs_to_operand_frame_with_work_v3
-- name    : BitDFT.ReaderHostFrame.reader_outputs_to_operand_frame_with_work_v3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T18:09:28.542379+00:00
-- url     : https://prove2.me/theorems/eccfe29a-586d-4342-9679-f181ceead74b
-- title:
--   Reader frame initializes every tracked multiplier work tape (v3)
-- statement:
--   If the Fourier reader has written a signed coordinate and the header reader has retained the binary dimension, the shared host frame places both words at the operand staging tapes. Every tracked multiplier work tape is also in its genuine blank configuration, with its head at cell 1. This supplies the complete initial-frame interface needed to start the tracked multiplication machine.
-- source:
--   Proves the common-host reader frame with all tracked multiplier work tapes explicitly blank and their heads reset. Helper definitions are imported from the shared support module so the target and its proof do not redeclare them.

import Definitions.Def_BitDFT_ReaderHostFrame_WorkSupport_v2
set_option autoImplicit false
noncomputable section
namespace BitDFT.ReaderHostFrame
open IntMul BitDFT.DedicatedTapeBanks BitDFT.BankedTripleAlphabetHost

theorem reader_outputs_to_operand_frame_with_work_v3 (A M H : MultitapeTM)
    (hH4 : 3 < H.k) (cF : A.Cfg) (cH : H.Cfg) (j : Fin A.k)
    (hj : 1 ≤ j.val) (dimension low : List Bool) (sign high : Bool)
    (hcoord : cF.cells j = A.tapeOf (([sign, high] ++ low).map A.bitSym))
    (hdim : cH.cells ⟨3, hH4⟩ = H.tapeOf (dimension.map H.bitSym))
    (hdimHead : cH.head ⟨3, hH4⟩ = dimension.length + 1) :
    ∃ base : (BankedOperandStage.controller A M H j hj).machine.Cfg,
      base.cells (BankedOperandStage.dimensionTape A M H) =
        (host A M H).tapeOf (dimension.map (host A M H).bitSym) ∧
      base.head (BankedOperandStage.dimensionTape A M H) = dimension.length + 1 ∧
      base.cells (BankedOperandStage.coordinateTape A M H j) =
        (host A M H).tapeOf (([sign, high] ++ low).map (host A M H).bitSym) ∧
      base.head (BankedOperandStage.coordinateTape A M H j) = low.length + 3 ∧
      ∀ i : Fin (tracked M).k, 2 ≤ i.val →
        base.cells (multiplierTapeRoute A M H i) = (host A M H).tapeOf [] ∧
        base.head (multiplierTapeRoute A M H i) = 1 := by sorry
