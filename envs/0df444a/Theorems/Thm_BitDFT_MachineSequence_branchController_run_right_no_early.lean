-- Prove2me | Theorems.Thm_BitDFT_MachineSequence_branchController_run_right_no_early
-- name    : BitDFT.MachineSequence.branchController_run_right_no_early
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T22:15:26.35546+00:00
-- url     : https://prove2.me/theorems/ba28ef2c-cfd4-42c0-921f-c6c1505c9da1
-- title:
--   Exact alternate-branch run even if it halts early
-- statement:
--   If a conditional controller selects its right branch and that branch reaches its exit after $t$ steps, the branch may have reached its frozen exit earlier. The combined controller nevertheless reaches the common exit after exactly $t+2$ steps and has the same tape contents and head positions as the selected branch after $t$ steps. This removes the need for a separate no-early-exit invariant on the right branch.
-- source:
--   Symmetric frozen-exit strengthening of the finite conditional-controller run theorem.

import Definitions.Def_BitDFT_BranchController
import Mathlib.Tactic
set_option autoImplicit false
open IntMul

theorem BitDFT.MachineSequence.branchController_run_right_no_early {M : MultitapeTM} (source : Fin M.k)
    (test : M.Sym → Bool) (P Q : Controller M) (t : ℕ) (c : Q.machine.Cfg)
    (hentry : c.state = Q.entry)
    (hselect : test (c.cells source (c.head source)) = false)
    (hexit : (Q.machine.step^[t] c).state = Q.exit) :
    (branchController source test P Q).machine.step^[(t+2)]
      (branchChooseCfg c.cells c.head) =
        branchDoneCfg (source := source) (test := test) (P := P) (Q := Q)
          (Q.machine.step^[t] c).cells (Q.machine.step^[t] c).head := by sorry
