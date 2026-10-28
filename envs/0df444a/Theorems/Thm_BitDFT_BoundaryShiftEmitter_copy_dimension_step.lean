-- Prove2me | Theorems.Thm_BitDFT_BoundaryShiftEmitter_copy_dimension_step
-- name    : BitDFT.BoundaryShiftEmitter.copy_dimension_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T21:27:37.449379+00:00
-- url     : https://prove2.me/theorems/89db1def-dec4-4354-a378-0b222ef7b655
-- title:
--   Copy one dimension bit into the output and advance both tapes
-- statement:
--   In the boundary-shift emitter, assume the dimension tape currently scans the next bit b, the output head is at the first blank after its existing output word, and the coordinate, dimension and output tapes are pairwise distinct and disjoint from the input tape. One transition copies b onto the output, advances the dimension and output heads, leaves the coordinate tape and all other tapes unchanged, and remains in the copy-dimension state.
-- source:
--   Direct one-transition proof for the published marker-protected boundary-shift emitter. This is the reusable body lemma for iterating over the binary dimension word in the rescaling controller.

import Definitions.Def_BitDFT_BoundaryShiftEmitter
import Mathlib.Tactic
import Mathlib.Data.List.GetD
set_option autoImplicit false
open BitDFT.BoundaryShiftEmitter IntMul

theorem BitDFT.BoundaryShiftEmitter.copy_dimension_step
    (N : MultitapeTM) (coordinate dimension output : Fin N.k)
    (hc : coordinate ≠ N.inTape) (hd : dimension ≠ N.inTape) (ho : output ≠ N.inTape)
    (hcd : coordinate ≠ dimension) (hco : coordinate ≠ output) (hdo : dimension ≠ output)
    (base : (control N coordinate dimension output hc hd ho hcd hco hdo).machine.Cfg)
    (coordWord pre : List Bool) (b : Bool) (rest out : List Bool)
    (coordHead : ℕ) :
    let C := control N coordinate dimension output hc hd ho hcd hco hdo
    C.machine.step (frame coordinate dimension output hc hd ho hcd hco hdo base
      .copyDimension coordWord (pre ++ [b] ++ rest) out coordHead (pre.length+1) (out.length+1)) =
    frame coordinate dimension output hc hd ho hcd hco hdo base
      .copyDimension coordWord (pre ++ [b] ++ rest) (out ++ [b]) coordHead
      (pre.length+2) (out.length+2) := by sorry
