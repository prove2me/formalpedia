-- Prove2me | Theorems.Thm_BitDFT_BankedOperandStageProof_coordinate_pair_output_buffer
-- name    : BitDFT.BankedOperandStageProof.coordinate_pair_output_buffer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T16:44:54.836024+00:00
-- url     : https://prove2.me/theorems/dded3b4f-02c9-47e8-80d2-e699ee4951e8
-- title:
--   The staged operand pair occupies the exact multiplier input buffer
-- statement:
--   After copying the q-bit coordinate behind the padded binary dimension and separator, the staging controller’s output tape contains exactly a blank sentinel followed by the complete operand-pair encoding. This identifies the payload cells directly, including the zero-padding needed when the dimension uses fewer than q bits.
-- source:
--   A cell-level consequence of the accepted exact coordinate-pair staging run.

import Definitions.Def_BitDFT_OperandStage
import Definitions.Def_BitDFT_BankedOperandStageProofSupport
import Theorems.Thm_BitDFT_BankedOperandStageProof_coordinate_pair_to_halt
import Mathlib.Data.List.GetD
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace BitDFT.BankedOperandStageProof
open IntMul BitDFT.OperandStage BitDFT.MachineSequence BitDFT.BankedOperandStageProofSupport

theorem coordinate_pair_output_buffer {N : MultitapeTM}
    (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (dimension low : List Bool) (sign high : Bool)
    (hdimCells : base.cells dim = N.tapeOf (dimension.map N.bitSym))
    (hdimHead : base.head dim = dimension.length + 1)
    (hcoordCells : base.cells coord = N.tapeOf (([sign, high] ++ low).map N.bitSym))
    (hcoordHead : base.head coord = low.length + 3)
    (hq : dimension.length ≤ low.length)
    (hpad : ∀ p, 1 ≤ p →
      (N.tapeOf (N.blank :: List.replicate low.length N.zero)) p ≠ N.startSym)
    (hdimBlank : (N.tapeOf (dimension.map N.bitSym))
      (dimension.length + 1) = N.blank) :
    ((machine N coord dim out hc hd ho hcd hco hdo).step ^[
      2 * dimension.length + 3 * low.length + 14]
      (initialStageFrame coord dim out hc hd ho hcd hco hdo base
        ([sign, high] ++ low))).cells out =
      N.tapeOf (N.blank ::
        (List.replicate (low.length - dimension.length) N.zero ++
          dimension.map N.bitSym ++ [N.sep] ++ low.map N.bitSym)) := by sorry
