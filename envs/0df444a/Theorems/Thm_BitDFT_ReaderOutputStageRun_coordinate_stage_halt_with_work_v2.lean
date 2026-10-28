-- Prove2me | Theorems.Thm_BitDFT_ReaderOutputStageRun_coordinate_stage_halt_with_work_v2
-- name    : BitDFT.ReaderOutputStageRun.coordinate_stage_halt_with_work_v2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T18:03:52.812994+00:00
-- url     : https://prove2.me/theorems/36bb17b7-7b84-4f2d-9451-b3915156422c
-- title:
--   Coordinate staging preserves a clean multiplier work bank (v2)
-- statement:
--   Assume the operand staging controller begins with a correctly encoded dimension and signed coordinate, and every tracked multiplier work tape is blank with its head at cell 1. Then the controller halts after its exact prescribed number of steps, writes the padded dimension and coordinate into the output buffer, and preserves every multiplier work tape in that blank initial state.
-- source:
--   A conditional exact-run result: compose the proved coordinate-pair staging run and output-buffer theorem with the proved frame invariant for all tapes outside the staging controller work set. The clean work-bank condition is explicit so it can be discharged by the reader-frame theorem separately. Reissued because the first target ID is not addressable.

import Definitions.Def_BitDFT_BankedOperandStageProofSupport
import Definitions.Def_BitDFT_BankedTripleAlphabetHost
import Definitions.Def_BitDFT_BankedOperandStage
import Definitions.Def_BitDFT_TripleAlphabet
import Definitions.Def_IntMul_TrackedBankedCall
import Definitions.Def_BitDFT_OperandStage
import Theorems.Thm_BitDFT_OperandStage_run_preserves_other_tape
import Theorems.Thm_BitDFT_BankedOperandStageProof_coordinate_pair_to_halt
import Theorems.Thm_BitDFT_BankedOperandStageProof_coordinate_pair_output_buffer
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open IntMul BitDFT.OperandStage BitDFT.MachineSequence
namespace BitDFT.ReaderHostFrame
open IntMul BitDFT.DedicatedTapeBanks BitDFT.BankedTripleAlphabetHost
abbrev tracked (M : MultitapeTM) := IntMul.TrackedBankedCall.machine M
abbrev host (A M H : MultitapeTM) := BankedTripleAlphabetHost.multiplierMachine A (tracked M) H

def multiplierTapeRoute (A M H : MultitapeTM) (i : Fin (tracked M).k) :
    Fin (DedicatedTapeBanks.width A (tracked M) H) := by
  let X := tracked M
  have hX : X.k ≤ DedicatedTapeBanks.width A X H := by
    rw [DedicatedTapeBanks.width_eq_sum]
    have hA := A.two_le_k
    have hX := X.two_le_k
    have hH := H.two_le_k
    omega
  let r := DedicatedTapeBanks.width A X H - X.k
  let h : X.k + r = DedicatedTapeBanks.width A X H := Nat.add_sub_of_le hX
  exact BankedTripleAlphabetHost.route A X H
    (DedicatedTapeBanks.multiplierOffset A X H)
    (by
      have hA := A.two_le_k
      have hX := X.two_le_k
      have hH := H.two_le_k
      dsimp [DedicatedTapeBanks.multiplierOffset, DedicatedTapeBanks.tail]
      omega)
    (Fin.cast h (TapeExtension.oldTape X r i))


end BitDFT.ReaderHostFrame
namespace BitDFT.ReaderOutputStageRun
def entryFrame {N : MultitapeTM} (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (source : List Bool) :
    (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo).machine.Cfg where
  state := .skipSign
  cells := fun i => if i = coord then N.tapeOf (source.map N.bitSym)
    else if i = out then N.tapeOf [] else base.cells i
  head := fun i => if i = coord ∨ i = out then 1 else base.head i

theorem coordinate_stage_halt_with_work_v2
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
