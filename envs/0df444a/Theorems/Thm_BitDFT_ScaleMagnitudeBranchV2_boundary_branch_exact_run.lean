-- Prove2me | Theorems.Thm_BitDFT_ScaleMagnitudeBranchV2_boundary_branch_exact_run
-- name    : BitDFT.ScaleMagnitudeBranchV2.boundary_branch_exact_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T22:13:46.950772+00:00
-- url     : https://prove2.me/theorems/212c5af7-3885-4673-867c-32a26cb7fdcf
-- title:
--   Exact run of the boundary branch in the magnitude scaler
-- statement:
--   Suppose a separate flag tape identifies the high-magnitude-bit case for one signed coordinate. The combined scaler selects the exact boundary-shift emitter, runs it on the sign, high bit, low bits, and dimension bits, and reaches the shared branch exit in exactly $d+ell+6$ steps, where $d$ is the dimension-field length and $ell$ is the low-bit-field length. Its final tape contents and head positions are exactly those of the boundary emitter after its $d+ell+4$-step run. This theorem instantiates the generic conditional-controller composition with the concrete boundary-scaling machine.
-- source:
--   Composition of the published separate-flag scaler controller, accepted boundary-shift emitter run, and exact conditional-controller run theorem.

import Definitions.Def_BitDFT_ScaleMagnitudeBranchV2
import Mathlib.Tactic
set_option autoImplicit false
open BitDFT.ScaleMagnitudeBranchV2 BitDFT.BoundaryShiftEmitter BitDFT.MachineSequence IntMul

theorem BitDFT.ScaleMagnitudeBranchV2.boundary_branch_exact_run {N : MultitapeTM}
    (selector coordinate dimension output : Fin N.k) (isHigh : N.Sym → Bool)
    (hc : coordinate ≠ N.inTape) (hd : dimension ≠ N.inTape) (ho : output ≠ N.inTape)
    (hcd : coordinate ≠ dimension) (hco : coordinate ≠ output) (hdo : dimension ≠ output)
    (hsc : selector ≠ coordinate) (hsd : selector ≠ dimension) (hso : selector ≠ output)
    (base : (BoundaryShiftEmitter.control N coordinate dimension output hc hd ho hcd hco hdo).machine.Cfg)
    (sign high : Bool) (dimensionBits low : List Bool)
    (hflag : isHigh (base.cells selector (base.head selector)) = true) :
    let P := BoundaryShiftEmitter.control N coordinate dimension output hc hd ho hcd hco hdo
    let initial := BoundaryShiftEmitter.frame coordinate dimension output hc hd ho hcd hco hdo
      base .sign ([sign, high] ++ low) dimensionBits [] 1 1 1
    (machine N selector coordinate dimension output isHigh hc hd ho hcd hco hdo hsc hsd hso).step^[dimensionBits.length+low.length+6]
      (branchChooseCfg initial.cells initial.head) =
      branchDoneCfg (source := selector) (test := isHigh)
        (P := BoundaryShiftEmitter.control N coordinate dimension output hc hd ho hcd hco hdo)
        (Q := MachineSequence.native N)
        (P.machine.step^[dimensionBits.length+low.length+4] initial).cells
        (P.machine.step^[dimensionBits.length+low.length+4] initial).head := by sorry
