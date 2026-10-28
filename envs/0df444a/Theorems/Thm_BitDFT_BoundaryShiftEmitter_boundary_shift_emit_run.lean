-- Prove2me | Theorems.Thm_BitDFT_BoundaryShiftEmitter_boundary_shift_emit_run
-- name    : BitDFT.BoundaryShiftEmitter.boundary_shift_emit_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T21:36:50.418727+00:00
-- url     : https://prove2.me/theorems/2c6de0b7-a7d2-4911-b48d-d77610129f9a
-- title:
--   The boundary-shift emitter writes the exact shifted field in dimension length plus low-field length plus four steps
-- statement:
--   Let a signed coordinate field contain sign bit s, high bit h, and a lower binary word of length ℓ; let the dimension be encoded by a binary word of length d. The published boundary-shift controller copies s, skips h, copies the dimension word, and writes ℓ zero bits. Its exact output is the sign bit followed by the dimension bits and ℓ zeros, and the controller halts after exactly d + ℓ + 4 transitions. This is the machine-run component used to handle the exceptional magnitude at the scaling boundary.
-- source:
--   Formal exact-run theorem for the published marker-protected boundary-shift emitter. The proof composes its two setup transitions, an induction over dimension bits, the phase transition, an induction over lower coordinate bits, and the final blank check.

import Definitions.Def_BitDFT_BoundaryShiftEmitter
import Mathlib.Tactic
import Mathlib.Data.List.GetD
set_option autoImplicit false
open BitDFT.BoundaryShiftEmitter IntMul

theorem BitDFT.BoundaryShiftEmitter.boundary_shift_emit_run
    (N : MultitapeTM) (coordinate dimension output : Fin N.k)
    (hc : coordinate ≠ N.inTape) (hd : dimension ≠ N.inTape) (ho : output ≠ N.inTape)
    (hcd : coordinate ≠ dimension) (hco : coordinate ≠ output) (hdo : dimension ≠ output)
    (base : (control N coordinate dimension output hc hd ho hcd hco hdo).machine.Cfg)
    (sign high : Bool) (dimensionBits low : List Bool) :
    let C := control N coordinate dimension output hc hd ho hcd hco hdo
    let initial := frame coordinate dimension output hc hd ho hcd hco hdo base
      .sign ([sign,high] ++ low) dimensionBits [] 1 1 1
    let final := frame coordinate dimension output hc hd ho hcd hco hdo base
      .halt ([sign,high] ++ low) dimensionBits
      ([sign] ++ dimensionBits ++ List.replicate low.length false)
      (low.length+3) (dimensionBits.length+1)
      (dimensionBits.length+low.length+2)
    C.machine.step^[dimensionBits.length+low.length+4] initial = final := by sorry
