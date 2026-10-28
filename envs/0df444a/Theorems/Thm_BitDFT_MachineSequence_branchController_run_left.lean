-- Prove2me | Theorems.Thm_BitDFT_MachineSequence_branchController_run_left
-- name    : BitDFT.MachineSequence.branchController_run_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T21:58:16.506679+00:00
-- url     : https://prove2.me/theorems/f5c9251b-1a47-4d3a-adac-7d8cca3140c2
-- title:
--   Exact run of the selected controller branch
-- statement:
--   Let two finite controllers operate on the same multitape machine. If the scanned symbol selects the left controller, and that controller starts at its entry state, avoids its exit for the first $t$ steps, and reaches its exit at step $t$, then the combined controller follows exactly that run and halts at the shared exit after $t+2$ total steps. Every tape cell and head position at the shared exit agrees with the selected controller’s final configuration. This is the precise run-composition fact used to join the low-magnitude and boundary cases in output rescaling.
-- source:
--   Finite-state controller composition over the IntMul.MultitapeTM step semantics; companion to the BitDFT output-rescaling machine construction.

import Definitions.Def_BitDFT_BranchController
import Mathlib.Tactic
open IntMul

theorem BitDFT.MachineSequence.branchController_run_left {M : MultitapeTM} (source : Fin M.k)
    (test : M.Sym → Bool) (P Q : Controller M) (t : ℕ) (c : P.machine.Cfg)
    (hentry : c.state = P.entry)
    (hselect : test (c.cells source (c.head source)) = true)
    (hfirst : ∀ s < t, (P.machine.step^[s] c).state ≠ P.exit)
    (hexit : (P.machine.step^[t] c).state = P.exit) :
    (branchController source test P Q).machine.step^[(t+2)]
      (branchChooseCfg c.cells c.head) =
        branchDoneCfg (source := source) (test := test) (P := P) (Q := Q)
          (P.machine.step^[t] c).cells (P.machine.step^[t] c).head := by sorry
