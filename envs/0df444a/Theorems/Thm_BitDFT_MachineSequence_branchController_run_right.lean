-- Prove2me | Theorems.Thm_BitDFT_MachineSequence_branchController_run_right
-- name    : BitDFT.MachineSequence.branchController_run_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T21:59:31.653803+00:00
-- url     : https://prove2.me/theorems/73d35a83-6a52-42d2-879c-316eab428078
-- title:
--   Exact run of the alternate controller branch
-- statement:
--   Let two finite controllers operate on the same multitape machine. If the scanned symbol selects the right controller, and that controller starts at its entry state, avoids its exit for the first $t$ steps, and reaches its exit at step $t$, then the combined controller follows exactly that run and halts at the shared exit after $t+2$ total steps. Every tape cell and head position at the shared exit agrees with the selected controller’s final configuration. This is the companion run-composition fact for conditional machine branches.
-- source:
--   Finite-state controller composition over the IntMul.MultitapeTM step semantics; companion to the BitDFT output-rescaling machine construction.

import Definitions.Def_BitDFT_BranchController
import Mathlib.Tactic
open BitDFT.MachineSequence IntMul

theorem BitDFT.MachineSequence.branchController_run_right {M : MultitapeTM} (source : Fin M.k)
    (test : M.Sym → Bool) (P Q : Controller M) (t : ℕ) (c : Q.machine.Cfg)
    (hentry : c.state = Q.entry)
    (hselect : test (c.cells source (c.head source)) = false)
    (hfirst : ∀ s < t, (Q.machine.step^[s] c).state ≠ Q.exit)
    (hexit : (Q.machine.step^[t] c).state = Q.exit) :
    (branchController source test P Q).machine.step^[(t+2)]
      (branchChooseCfg c.cells c.head) =
        branchDoneCfg (source := source) (test := test) (P := P) (Q := Q)
          (Q.machine.step^[t] c).cells (Q.machine.step^[t] c).head := by sorry
