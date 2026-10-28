-- Prove2me | Theorems.Thm_BitDFT_BoundaryShiftEmitter_boundary_shift_emit_sign_step
-- name    : BitDFT.BoundaryShiftEmitter.boundary_shift_emit_sign_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T21:09:39.851991+00:00
-- url     : https://prove2.me/theorems/52d6bfd4-4303-40af-8a34-e7db6f20d220
-- title:
--   The sign phase copies one signed coordinate bit
-- statement:
--   When the boundary-shift emitter starts with its coordinate head on the sign bit and its output head at the first blank cell, one transition copies the sign bit to the output and advances the coordinate and output heads. It leaves the dimension tape, all other cells, and all other heads unchanged.
-- source:
--   One-step trace lemma for the finite-state boundary-shift output controller used by the integer-multiplication to finite-precision DFT rescaling construction.

import Definitions.Def_BitDFT_BoundaryShiftEmitter
import Mathlib.Tactic
import Mathlib.Data.List.GetD
set_option autoImplicit false
set_option maxHeartbeats 0
namespace BitDFT.BoundaryShiftEmitter
open IntMul

theorem boundary_shift_emit_sign_step
    (N : MultitapeTM) (coordinate dimension output : Fin N.k)
    (hc : coordinate ≠ N.inTape) (hd : dimension ≠ N.inTape) (ho : output ≠ N.inTape)
    (hcd : coordinate ≠ dimension) (hco : coordinate ≠ output) (hdo : dimension ≠ output)
    (base : (control N coordinate dimension output hc hd ho hcd hco hdo).machine.Cfg)
    (sign high : Bool) (low dimensionBits : List Bool) :
    let C := control N coordinate dimension output hc hd ho hcd hco hdo
    C.machine.step (frame coordinate dimension output hc hd ho hcd hco hdo base
      .sign ([sign, high] ++ low) dimensionBits [] 1 1 1) =
    frame coordinate dimension output hc hd ho hcd hco hdo base
      .skipHigh ([sign, high] ++ low) dimensionBits [sign] 2 1 2 := by sorry
