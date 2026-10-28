-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_binaryTapePrograms_semantics
-- name    : CountingMatroid.Bridge.binaryTapePrograms_semantics
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T19:16:55.167981+00:00
-- url     : https://prove2.me/theorems/349b4717-9376-4cc8-8732-03846b7e79cd
-- title:
--   The two-stack programs implement head-relative tape shifts
-- statement:
--   For any represented binary tape, the verified right-move and left-move register programs produce stacks whose decoded cells are exactly the original tape viewed relative to the new head. Every cell is accounted for, including blank cells beyond either finite stack.
-- source:
--   Use the accepted exact stack invariants for both programs. The list-index lemmas show that prepending, dropping the consumed head, and treating an absent stack entry as false correspond exactly to shifting the coordinate frame by one cell.

import Mathlib
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_BinaryTapeSemantics
import Theorems.Thm_CountingMatroid_Bridge_binaryTapeMoveRightProgram_correct
import Theorems.Thm_CountingMatroid_Bridge_binaryTapeMoveLeftProgram_correct

set_option autoImplicit false
set_option maxHeartbeats 800000
open OAI.CommonBasesFPRAS

theorem CountingMatroid.Bridge.binaryTapePrograms_semantics {n : ℕ}
    (O : IndependenceOracle n) (bits : ℕ → Bool)
    (cR : MachineConfig 0 6) (cL : MachineConfig 0 17)
    (left right : List Bool)
    (hcR : cR.control.val = 0) (hoR : cR.output = none)
    (h6R : cR.registers 6 = left) (h7R : cR.registers 7 = right)
    (hcL : cL.control.val = 0) (hoL : cL.output = none)
    (h6L : cL.registers 6 = left) (h7L : cL.registers 7 = right) :
    let outR := execution binaryTapeMoveRightProgram O cR bits 2
    let outL := execution binaryTapeMoveLeftProgram O cL bits 4
    (binaryTapeAt (outR.registers 6) (outR.registers 7) (.left 0) =
          binaryTapeAt left right (.right 0) ∧
        (∀ i, binaryTapeAt (outR.registers 6) (outR.registers 7) (.left (i + 1)) =
          binaryTapeAt left right (.left i)) ∧
        (∀ i, binaryTapeAt (outR.registers 6) (outR.registers 7) (.right i) =
          binaryTapeAt left right (.right (i + 1)))) ∧
    ((∀ i, binaryTapeAt (outL.registers 6) (outL.registers 7) (.left i) =
          binaryTapeAt left right (.left (i + 1))) ∧
        binaryTapeAt (outL.registers 6) (outL.registers 7) (.right 0) =
          binaryTapeAt left right (.left 0) ∧
        (∀ i, binaryTapeAt (outL.registers 6) (outL.registers 7) (.right (i + 1)) =
          binaryTapeAt left right (.right i))) := by
  sorry
