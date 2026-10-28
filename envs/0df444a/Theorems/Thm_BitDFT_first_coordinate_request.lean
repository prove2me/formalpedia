-- Prove2me | Theorems.Thm_BitDFT_first_coordinate_request
-- name    : BitDFT.first_coordinate_request
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T19:02:25.373698+00:00
-- url     : https://prove2.me/theorems/50ba37f7-51f6-4c86-aaba-24c687f1ecd7
-- title:
--   Extract the first signed coordinate starting from the original Fourier request
-- statement:
--   For positive n and b, let q=b+3 lg(n)+5 and let y be the canonical binary representation of q. Suppose an arbitrary child machine returns a sign bit followed by x after T transitions on the precision-q Fourier input, with at least val(y)+1 magnitude bits available. Starting from the original requested input, the combined machine reaches the specified complete first-coordinate extraction state within 193 n q+11 T+6(val(y)+1)+4|y|+7 transitions. The full final state includes the copied signed magnitude, advanced vector and scratch heads, and restored precision descriptors. Multiplication and output rescaling are subsequent stages.
-- source:
--   Actual-machine initialization for the exact Fourier output scaler. Coordinate multiplication and serialization remain separate obligations.

import Definitions.Def_BitDFT_FirstCoordinate
open BitDFT.FirstCoordinate BitDFT IntMul MachineSequence

theorem BitDFT.first_coordinate_request (M : MultitapeTM) (n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) (U : Fin n → ℤ × ℤ)
    (T : ℕ)
    (halt : (M.step^[T] (M.initCfg (fourierInput (guardPrecision n b) U) [])).state = M.qHalt)
    (sign : Bool) (x : List Bool)
    (out : (M.step^[T] (M.initCfg (fourierInput (guardPrecision n b) U) [])).cells M.outTape = M.tapeOf ((sign::x).map M.bitSym))
    (hx : val (bin (guardPrecision n b).size (guardPrecision n b))+1 ≤ x.length) :
    let q := guardPrecision n b
    let y := bin q.size q
    ∃ t v,
      let c := VectorReady.final M (requestedInput b U)
        (NativeChildOutput.final M (ChildCall.final M
          (CallerReady.final (ChildCall.child M) M.k (RewriteInput.final n b (encVector (q+1) U) v)
            (fourierInput q U)) (fourierInput q U) T (sign::x)) (sign::x)) y
      t ≤ 193*n*q+11*T+6*(val y+1)+4*y.length+7 ∧ BinaryCounter.value v = q ∧
      (machine M).step^[t] ((machine M).initCfg (requestedInput b U) []) =
        final M c ((DescriptorSetup.machine.initCfg (requestedInput b U) []).cells 0)
          (c.head (VectorReady.machine M).inTape) sign x y := by sorry
