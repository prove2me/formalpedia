-- Prove2me | Theorems.Thm_BitDFT_coordinate_readable
-- name    : BitDFT.coordinate_readable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T19:08:26.76827+00:00
-- url     : https://prove2.me/theorems/be7ef788-5aa8-4d3e-9e48-eb3789e3445f
-- title:
--   Return to the scratch sign bit with a charged linear rewind
-- statement:
--   Suppose first-coordinate extraction reaches its specified final configuration in T steps. For descriptor y, the composed machine reaches the specified readable-record configuration within T+val(y)+5 steps. Its scratch tape contains exactly the copied sign and next val(y)+1 magnitude bits, and the scratch head is at the first data cell. The complete final configuration preserves all other tape contents and head positions. The bound includes the controller handoff and every rewind transition.
-- source:
--   Actual-machine initialization for the exact Fourier output scaler. Coordinate multiplication and serialization remain separate obligations.

import Definitions.Def_BitDFT_CoordinateReadable
open BitDFT.CoordinateReadable BitDFT IntMul MachineSequence

theorem BitDFT.coordinate_readable (M : MultitapeTM) (c : (VectorReady.machine M).Cfg)
    (rootCells : ℕ → TapeCopy.Sym) (rootHead : ℕ) (sign : Bool) (x y input extra : List Bool) (T : ℕ)
    (hrun : (preparation M).step^[T] ((preparation M).initCfg input extra) =
      FirstCoordinate.final M c rootCells rootHead sign x y) :
    ∃ t : ℕ, t ≤ T+val y+5 ∧
      (machine M).step^[t] ((machine M).initCfg input extra) = final M c rootCells rootHead sign x y ∧
      ((machine M).step^[t] ((machine M).initCfg input extra)).cells (scratch M) =
        (machine M).tapeOf ((sign::x.take (val y+1)).map (machine M).bitSym) ∧
      ((machine M).step^[t] ((machine M).initCfg input extra)).head (scratch M) = 1 := by sorry
