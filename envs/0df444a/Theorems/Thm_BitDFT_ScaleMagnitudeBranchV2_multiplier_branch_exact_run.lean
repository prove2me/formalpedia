-- Prove2me | Theorems.Thm_BitDFT_ScaleMagnitudeBranchV2_multiplier_branch_exact_run
-- name    : BitDFT.ScaleMagnitudeBranchV2.multiplier_branch_exact_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T22:16:45.428631+00:00
-- url     : https://prove2.me/theorems/e00c027f-8c34-47e2-87ae-1a9b91217309
-- title:
--   Exact run of the multiplier branch in the magnitude scaler
-- statement:
--   Suppose a separate flag tape identifies the low-magnitude case, and the native multiplier machine runs from its start state to its halt state in $t$ steps. The combined magnitude scaler selects that machine, follows its entire run, and reaches the shared branch exit after exactly $t+2$ steps, preserving the multiplier’s final tape contents and head positions. This is the multiplier-side companion to the exact boundary-shift branch theorem.
-- source:
--   Composition of the published separate-flag scaler controller and generic exact conditional-controller run theorem.

import Definitions.Def_BitDFT_ScaleMagnitudeBranchV2
import Mathlib.Tactic
set_option autoImplicit false
open BitDFT BitDFT.ScaleMagnitudeBranchV2 BitDFT.BoundaryShiftEmitter BitDFT.MachineSequence IntMul

theorem BitDFT.ScaleMagnitudeBranchV2.multiplier_branch_exact_run {N : MultitapeTM}
    (selector coordinate dimension output : Fin N.k) (isHigh : N.Sym → Bool)
    (hc : coordinate ≠ N.inTape) (hd : dimension ≠ N.inTape) (ho : output ≠ N.inTape)
    (hcd : coordinate ≠ dimension) (hco : coordinate ≠ output) (hdo : dimension ≠ output)
    (hsc : selector ≠ coordinate) (hsd : selector ≠ dimension) (hso : selector ≠ output)
    (t : ℕ) (c : N.Cfg) (hentry : c.state = N.qStart)
    (hflag : isHigh (c.cells selector (c.head selector)) = false)
    (hexit : (N.step^[t] c).state = N.qHalt) :
    (machine N selector coordinate dimension output isHigh hc hd ho hcd hco hdo hsc hsd hso).step^[t+2]
      (branchChooseCfg c.cells c.head) =
      branchDoneCfg (source := selector) (test := isHigh)
        (P := BoundaryShiftEmitter.control N coordinate dimension output hc hd ho hcd hco hdo)
        (Q := MachineSequence.native N) (N.step^[t] c).cells (N.step^[t] c).head := by sorry
