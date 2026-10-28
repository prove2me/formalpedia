-- Prove2me | Theorems.Thm_BitDFT_ScaleMagnitudeBranchV2_multiplier_branch_output
-- name    : BitDFT.ScaleMagnitudeBranchV2.multiplier_branch_output
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T22:36:56.699271+00:00
-- url     : https://prove2.me/theorems/98f24b3f-d94c-4619-811f-5a8ac7d852e8
-- title:
--   Low-magnitude branch preserves the multiplier output tape
-- statement:
--   Suppose the low-magnitude case selects the multiplier branch, and the multiplier halts after $t$ steps. The composed branch controller preserves the multiplier's output tape exactly:
--
--   $$	ext{output}_{mathrm{branch}}=	ext{output}_{mathrm{multiplier}}.$$
--
--   This output-frame result lets the branch's exact-run theorem serve as a component in the full scaler composition.
-- source:
--   Projection of the accepted exact multiplier-branch run onto its designated output tape.

import Definitions.Def_BitDFT_ScaleMagnitudeBranchV2
import Definitions.Def_BitDFT_BoundaryShiftEmitter
import Definitions.Def_BitDFT_MachineSequence
import Mathlib.Tactic
set_option autoImplicit false
open BitDFT BitDFT.ScaleMagnitudeBranchV2 BitDFT.BoundaryShiftEmitter BitDFT.MachineSequence IntMul

theorem BitDFT.ScaleMagnitudeBranchV2.multiplier_branch_output {N : MultitapeTM}
    (selector coordinate dimension output : Fin N.k) (isHigh : N.Sym → Bool)
    (hc : coordinate ≠ N.inTape) (hd : dimension ≠ N.inTape) (ho : output ≠ N.inTape)
    (hcd : coordinate ≠ dimension) (hco : coordinate ≠ output) (hdo : dimension ≠ output)
    (hsc : selector ≠ coordinate) (hsd : selector ≠ dimension) (hso : selector ≠ output)
    (c : N.Cfg)
    (hentry : c.state = N.qStart)
    (hflag : isHigh (c.cells selector (c.head selector)) = false)
    (t : ℕ) (hhalt : (N.step^[t] c).state = N.qHalt) :
    ((machine N selector coordinate dimension output isHigh hc hd ho hcd hco hdo hsc hsd hso).step^[t+2]
      (branchChooseCfg c.cells c.head)).cells output = (N.step^[t] c).cells output := by sorry
