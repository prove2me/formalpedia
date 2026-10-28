-- Prove2me | Theorems.Thm_BitDFT_ScaleMagnitudeBranchV2_boundary_branch_output
-- name    : BitDFT.ScaleMagnitudeBranchV2.boundary_branch_output
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T22:25:28.753995+00:00
-- url     : https://prove2.me/theorems/91b0b43b-6db0-4237-9d19-f2179c858c44
-- title:
--   Boundary scaling branch emits the signed output field
-- statement:
--   In the exceptional magnitude case, the scaler uses a boundary-shift emitter instead of a multiplier call. If the signed input field has sign bit $s$, high bit $h$, and lower field of length $\ell$, while the dimension has binary encoding $D$, the selected branch leaves the exact output field on the designated tape:
--
--   $$s,D,0^{\ell}.$$
--
--   This result lifts the emitter’s exact trace through the shared conditional controller and confirms that the branch produces the required signed scaled encoding.
-- source:
--   Output-tape consequence of the accepted boundary-branch exact-run theorem and boundary-shift emitter trace.

import Definitions.Def_BitDFT_ScaleMagnitudeBranchV2
import Definitions.Def_BitDFT_BoundaryShiftEmitter
import Theorems.Thm_BitDFT_ScaleMagnitudeBranchV2_boundary_branch_exact_run
import Theorems.Thm_BitDFT_BoundaryShiftEmitter_boundary_shift_emit_run
import Mathlib.Tactic
set_option autoImplicit false
open IntMul BitDFT.MachineSequence

theorem BitDFT.ScaleMagnitudeBranchV2.boundary_branch_output
    {N : MultitapeTM}
    (selector coordinate dimension output : Fin N.k) (isHigh : N.Sym → Bool)
    (hc : coordinate ≠ N.inTape) (hd : dimension ≠ N.inTape)
    (ho : output ≠ N.inTape) (hcd : coordinate ≠ dimension)
    (hco : coordinate ≠ output) (hdo : dimension ≠ output)
    (hsc : selector ≠ coordinate) (hsd : selector ≠ dimension)
    (hso : selector ≠ output)
    (base : (BitDFT.BoundaryShiftEmitter.control N coordinate dimension output
      hc hd ho hcd hco hdo).machine.Cfg)
    (sign high : Bool) (dimensionBits low : List Bool)
    (hflag : isHigh (base.cells selector (base.head selector)) = true) :
    let P := BitDFT.BoundaryShiftEmitter.control N coordinate dimension output
      hc hd ho hcd hco hdo
    let initial := BitDFT.BoundaryShiftEmitter.frame coordinate dimension output
      hc hd ho hcd hco hdo base .sign ([sign, high] ++ low) dimensionBits [] 1 1 1
    let result := (branchController selector isHigh P (MachineSequence.native N)).machine.step^[dimensionBits.length + low.length + 6]
      (branchChooseCfg initial.cells initial.head)
    result.cells output = N.tapeOf
      (([sign] ++ dimensionBits ++ List.replicate low.length false).map N.bitSym) := by sorry
