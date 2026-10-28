-- Prove2me | Theorems.Thm_BitDFT_MachineSequence_branchController_run_left_no_early
-- name    : BitDFT.MachineSequence.branchController_run_left_no_early
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T22:09:43.509221+00:00
-- url     : https://prove2.me/theorems/4c8bd7fa-65aa-49b5-990f-9ce5cc60bbbc
-- title:
--   Exact selected-branch run even if the branch halts early
-- statement:
--   Let a conditional controller select its left branch, and suppose that branch reaches its exit after $t$ steps. The branch may reach its exit earlier and then remain halted. The combined controller still reaches the common exit after exactly $t+2$ steps, with the same tape contents and head positions as the branch after $t$ steps. This stronger composition lemma lets a caller use an exact run bound without separately proving that the branch never halts early.
-- source:
--   Strengthening of the finite conditional-controller run theorem using the frozen-exit semantics of IntMul.MultitapeTM.

import Definitions.Def_BitDFT_BranchController
import Mathlib.Tactic
set_option autoImplicit false
open IntMul

theorem BitDFT.MachineSequence.branchController_run_left_no_early {M : MultitapeTM} (source : Fin M.k)
    (test : M.Sym → Bool) (P Q : Controller M) (t : ℕ) (c : P.machine.Cfg)
    (hentry : c.state = P.entry)
    (hselect : test (c.cells source (c.head source)) = true)
    (hexit : (P.machine.step^[t] c).state = P.exit) :
    (branchController source test P Q).machine.step^[(t+2)]
      (branchChooseCfg c.cells c.head) =
        branchDoneCfg (source := source) (test := test) (P := P) (Q := Q)
          (P.machine.step^[t] c).cells (P.machine.step^[t] c).head := by sorry
