-- Prove2me | Theorems.Thm_BitDFT_native_child_output_correct
-- name    : BitDFT.native_child_output_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T17:37:02.161643+00:00
-- url     : https://prove2.me/theorems/1436b7f2-f6af-478c-b21d-d1b109a99e45
-- title:
--   Native arbitrary-child execution in at most 181nq+10T transitions
-- statement:
--   For positive n,b and q=b+3 lg(n)+5, suppose any finite child machine M halts on the Fourier input at precision q after T transitions with canonical binary output w. The constructed wrapper starts from the ordinary requested input and halts with exactly w on native output within 181nq+10T transitions. Its output head is at |w|+1, and the exact full final configuration is specified. All preprocessing, input preparation, child execution, cleanup, output shifting, and handoffs are charged. No regularity of a runtime function is assumed.
-- source:
--   Actual native I/O wrapper for an arbitrary Fourier child. This closes the input-rewriting and arbitrary-child invocation component; multiplier-based scaling and the normalized Fourier algorithm remain open components of the root theorem.

import Definitions.Def_BitDFT_NativeChildOutput
open BitDFT.NativeChildOutput BitDFT IntMul MachineSequence

theorem BitDFT.native_child_output_correct (M : MultitapeTM) (n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) (U : Fin n → ℤ × ℤ)
    (T : ℕ)
    (halt : (M.step^[T] (M.initCfg (fourierInput (guardPrecision n b) U) [])).state = M.qHalt)
    (w : List Bool)
    (out : (M.step^[T] (M.initCfg (fourierInput (guardPrecision n b) U) [])).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    let q := guardPrecision n b
    let x := fourierInput q U
    ∃ t v, t ≤ 181*n*q+10*T ∧
      (program M).step^[t] ((program M).initCfg (requestedInput b U) []) =
        final M (ChildCall.final M
          (CallerReady.final (ChildCall.child M) M.k (RewriteInput.final n b (encVector (q+1) U) v) x) x T w) w ∧
      (program M).HaltsWithOutput (requestedInput b U) [] t w ∧
      ((program M).step^[t] ((program M).initCfg (requestedInput b U) [])).head (program M).outTape = w.length+1 := by sorry
