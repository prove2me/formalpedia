-- Prove2me | Theorems.Thm_BitDFT_first_coordinate_execution
-- name    : BitDFT.first_coordinate_execution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T19:02:06.040161+00:00
-- url     : https://prove2.me/theorems/5c11969d-ae0d-4e01-99b9-dd9c1196787f
-- title:
--   Execute preparation and first signed-coordinate extraction with all handoffs charged
-- statement:
--   Suppose vector initialization halts in T steps with the specified vector, native input, and precision descriptors. If at least B=val(y)+1 magnitude bits follow its first sign bit, the combined machine reaches the full coordinate-extraction final configuration within T+6B+4|y|+7 steps. The overhead includes scratch allocation and head setup, controller handoffs, sign copying, magnitude copying, and descriptor restoration.
-- source:
--   Actual-machine initialization for the exact Fourier output scaler. Coordinate multiplication and serialization remain separate obligations.

import Definitions.Def_BitDFT_FirstCoordinate
open BitDFT.FirstCoordinate BitDFT IntMul MachineSequence

theorem BitDFT.first_coordinate_execution (M : MultitapeTM) (c : (VectorReady.machine M).Cfg)
    (input extra : List Bool) (T : ℕ)
    (hrun : (VectorReady.machine M).step^[T] ((VectorReady.machine M).initCfg input extra) = c)
    (hhalt : c.state = (VectorReady.machine M).qHalt)
    (rootCells : ℕ → TapeCopy.Sym) (rootHead : ℕ) (sign : Bool) (x y : List Bool)
    (hroot : c.cells ⟨0,by change 0 < 4+(M.k+3); omega⟩ = fun p => PreprocessorAlphabet.encode (VectorReady.machine M) (rootCells p))
    (hrootHead : c.head ⟨0,by change 0 < 4+(M.k+3); omega⟩ = rootHead)
    (hv : c.cells ⟨1,by change 1 < 4+(M.k+3); omega⟩ = (VectorReady.machine M).tapeOf ((sign::x).map (VectorReady.machine M).bitSym))
    (hvHead : c.head ⟨1,by change 1 < 4+(M.k+3); omega⟩ = 1)
    (hc : c.cells (DescriptorPlacement.counterTape M.k) = (VectorReady.machine M).tapeOf ((VectorReady.machine M).sep :: (y.map (VectorReady.machine M).bitSym ++ [(VectorReady.machine M).sep])))
    (hcHead : c.head (DescriptorPlacement.counterTape M.k) = y.length+1)
    (ht : c.cells (DescriptorPlacement.templateTape M.k) = (VectorReady.machine M).tapeOf ((VectorReady.machine M).sep :: (y.map (VectorReady.machine M).bitSym ++ [(VectorReady.machine M).sep])))
    (htHead : c.head (DescriptorPlacement.templateTape M.k) = y.length+1)
    (hx : val y+1 ≤ x.length) :
    ∃ t : ℕ, t ≤ T+6*(val y+1)+4*y.length+7 ∧
      (machine M).step^[t] ((machine M).initCfg input extra) = final M c rootCells rootHead sign x y := by sorry
