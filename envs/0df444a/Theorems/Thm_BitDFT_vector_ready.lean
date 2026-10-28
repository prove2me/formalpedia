-- Prove2me | Theorems.Thm_BitDFT_vector_ready
-- name    : BitDFT.vector_ready
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T18:41:34.42853+00:00
-- url     : https://prove2.me/theorems/2d8f4cd1-b12d-4aa0-906a-64b828e3cfc9
-- title:
--   Prepare the computed vector and precision descriptors for sequential extraction with a uniform clock
-- statement:
--   For positive n and b, let q be the guard precision. If an arbitrary child computes word w from the precision-q Fourier input in T transitions, the combined machine starts on the original request and halts with exactly w within 193 n q + 11 T transitions. Its output head is at cell one, both precision descriptor tapes are prepared as specified by the complete final configuration, and its retained arithmetic witness has value q. All input conversion, child execution, descriptor initialization, rewind steps, and handoffs are charged.
-- source:
--   Actual-machine initialization for the exact Fourier output scaler. Coordinate multiplication and serialization remain separate obligations.

import Definitions.Def_BitDFT_VectorReady
open BitDFT.VectorReady BitDFT IntMul MachineSequence

theorem BitDFT.vector_ready (M : MultitapeTM) (n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) (U : Fin n → ℤ × ℤ)
    (T : ℕ)
    (halt : (M.step^[T] (M.initCfg (fourierInput (guardPrecision n b) U) [])).state = M.qHalt)
    (w : List Bool)
    (out : (M.step^[T] (M.initCfg (fourierInput (guardPrecision n b) U) [])).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    let q := guardPrecision n b
    let x := fourierInput q U
    ∃ t v, t ≤ 193*n*q+11*T ∧ BinaryCounter.value v = q ∧
      (machine M).step^[t] ((machine M).initCfg (requestedInput b U) []) =
        final M (requestedInput b U)
          (NativeChildOutput.final M (ChildCall.final M
            (CallerReady.final (ChildCall.child M) M.k (RewriteInput.final n b (encVector (q+1) U) v) x) x T w) w)
          (bin q.size q) ∧
      (machine M).HaltsWithOutput (requestedInput b U) [] t w ∧
      ((machine M).step^[t] ((machine M).initCfg (requestedInput b U) [])).head (machine M).outTape = 1 := by sorry
