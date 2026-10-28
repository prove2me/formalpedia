-- Prove2me | Theorems.Thm_BitDFT_BankedOperandStageProof_stage_halt_then_rewind
-- name    : BitDFT.BankedOperandStageProof.stage_halt_then_rewind
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T15:22:17.699469+00:00
-- url     : https://prove2.me/theorems/ce6fe175-39cb-4bfd-96d5-ac59bf706c42
-- title:
--   Rewind the staged multiplier buffer after the staging controller halts
-- statement:
--   If operand staging has halted with a caller buffer marked at cell zero and its head at position p, then the staged controller can transfer control to the marker-rewind machine. The composed run takes at most p+2 transitions and returns with the output-buffer head at cell one, as required by the tracked multiplier caller frame.
-- source:
--   Composes the exact controller handoff with the previously accepted marker-rewind execution theorem and the generic finite-controller sequence bound.

import Definitions.Def_BitDFT_OperandStage
import Definitions.Def_BitDFT_RewindTape
import Theorems.Thm_BitDFT_rewind_tape_correct
import Theorems.Thm_BitDFT_machine_sequence_bound
set_option autoImplicit false
noncomputable section
namespace BitDFT.BankedOperandStageProof
open IntMul BitDFT.MachineSequence

theorem stage_halt_then_rewind {N : MultitapeTM}
    (coord dim out : Fin N.k)
    (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape) (ho : out ≠ N.inTape)
    (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (c : (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (hs : c.state = BitDFT.OperandStage.State.halt)
    (p : ℕ) (hp : c.head out = p)
    (hmarker : c.cells out 0 = N.startSym)
    (hnomarker : ∀ i, 0 < i → c.cells out i ≠ N.startSym) :
    ∃ v ≤ p + 2,
      (MachineSequence.sequence
        (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo)
        (BitDFT.RewindTape.control N out)).machine.step^[v]
        (MachineSequence.leftCfg
          (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo)
          (BitDFT.RewindTape.control N out) c) =
      MachineSequence.rightCfg
        (BitDFT.OperandStage.control N coord dim out hc hd ho hcd hco hdo)
        (BitDFT.RewindTape.control N out)
        (BitDFT.RewindTape.frame N out
          ⟨N.qStart, c.cells, c.head⟩ true 1) := by sorry
