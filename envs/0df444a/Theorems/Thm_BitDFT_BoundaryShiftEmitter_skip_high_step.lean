-- Prove2me | Theorems.Thm_BitDFT_BoundaryShiftEmitter_skip_high_step
-- name    : BitDFT.BoundaryShiftEmitter.skip_high_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T21:13:41.049779+00:00
-- url     : https://prove2.me/theorems/e986a191-ae60-4140-ae57-1403b1a9f57f
-- title:
--   The boundary-shift controller skips the high bit
-- statement:
--   After copying the sign bit, the boundary-shift controller advances the coordinate head over the high-magnitude bit and enters its dimension-copy phase. This transition leaves every tape cell and every other tape head unchanged.
-- source:
--   One-step trace lemma for the finite-state boundary-shift output controller used by the integer-multiplication to finite-precision DFT rescaling construction.

import Definitions.Def_BitDFT_BoundaryShiftEmitter
import Mathlib.Tactic
import Mathlib.Data.List.GetD
set_option autoImplicit false
set_option maxHeartbeats 0
namespace BitDFT.BoundaryShiftEmitter
open IntMul

theorem skip_high_step
    (N : MultitapeTM) (coordinate dimension output : Fin N.k)
    (hc : coordinate ≠ N.inTape) (hd : dimension ≠ N.inTape) (ho : output ≠ N.inTape)
    (hcd : coordinate ≠ dimension) (hco : coordinate ≠ output) (hdo : dimension ≠ output)
    (base : (control N coordinate dimension output hc hd ho hcd hco hdo).machine.Cfg)
    (sign high : Bool) (low dimensionBits : List Bool) :
    (machine N coordinate dimension output hc hd ho hcd hco hdo).step
      (frame coordinate dimension output hc hd ho hcd hco hdo base
        .skipHigh ([sign, high] ++ low) dimensionBits [sign] 2 1 2) =
      frame coordinate dimension output hc hd ho hcd hco hdo base
        .copyDimension ([sign, high] ++ low) dimensionBits [sign] 3 1 2 := by sorry
