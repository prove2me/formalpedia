-- Prove2me | Theorems.Thm_BitDFT_ReaderHostFrame_reader_outputs_to_operand_frame
-- name    : BitDFT.ReaderHostFrame.reader_outputs_to_operand_frame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T16:06:11.020024+00:00
-- url     : https://prove2.me/theorems/30ebfdc7-71f5-4819-947a-c82c81193cad
-- title:
--   Assemble the reader outputs in the multiplier host frame
-- statement:
--   Suppose the Fourier component has written the signed coordinate record `[sign, high] ++ low` on its designated tape, and the header parser has written the binary dimension on tape 3. In the disjoint-bank host, both records occur at the staging controller’s exact tape addresses. The parsed dimension is embedded at the retained dimension tape; the encoded signed coordinate is preserved in the Fourier bank. Thus one can construct the common host configuration required by the operand-pair staging run.
-- source:
--   Combines the accepted common-host tape projection and preservation theorems with the proved inverse-routing characterization for Fourier addresses. The returned frame is exactly the input interface of the accepted coordinate_pair_to_halt staging theorem, including its explicit heads.

import Definitions.Def_BitDFT_BankedTripleAlphabetHost
import Definitions.Def_BitDFT_BankedOperandStage
import Definitions.Def_BitDFT_TripleAlphabet
import Definitions.Def_IntMul_TrackedBankedCall
import Theorems.Thm_BitDFT_BankedTripleAlphabetHost_config_component_tape
import Theorems.Thm_BitDFT_BankedTripleAlphabetHost_config_extra_tape
import Theorems.Thm_BitDFT_header_inverse_fourier_bank
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open IntMul BitDFT.DedicatedTapeBanks BitDFT.BankedTripleAlphabetHost

theorem BitDFT.ReaderHostFrame.reader_outputs_to_operand_frame (A M H : MultitapeTM)
    (hH4 : 3 < H.k) (cF : A.Cfg) (cH : H.Cfg) (j : Fin A.k)
    (hj : 1 ≤ j.val) (dimension low : List Bool) (sign high : Bool)
    (hcoord : cF.cells j = A.tapeOf (([sign, high] ++ low).map A.bitSym))
    (hdim : cH.cells ⟨3, hH4⟩ = H.tapeOf (dimension.map H.bitSym))
    (hdimHead : cH.head ⟨3, hH4⟩ = dimension.length + 1) :
    ∃ base : (BankedOperandStage.controller A M H j hj).machine.Cfg,
      base.cells (BankedOperandStage.dimensionTape A M H) =
        (BankedTripleAlphabetHost.multiplierMachine A (IntMul.TrackedBankedCall.machine M) H).tapeOf (dimension.map (BankedTripleAlphabetHost.multiplierMachine A (IntMul.TrackedBankedCall.machine M) H).bitSym) ∧
      base.head (BankedOperandStage.dimensionTape A M H) = dimension.length + 1 ∧
      base.cells (BankedOperandStage.coordinateTape A M H j) =
        (BankedTripleAlphabetHost.multiplierMachine A (IntMul.TrackedBankedCall.machine M) H).tapeOf (([sign, high] ++ low).map
          (BankedTripleAlphabetHost.multiplierMachine A (IntMul.TrackedBankedCall.machine M) H).bitSym) ∧
      base.head (BankedOperandStage.coordinateTape A M H j) = low.length + 3 := by sorry
