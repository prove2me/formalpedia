-- Prove2me | Theorems.Thm_BitDFT_native_child_output_with_precision
-- name    : BitDFT.native_child_output_with_precision
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T18:26:51.201525+00:00
-- url     : https://prove2.me/theorems/4044567a-ed56-4fec-852d-65fdc0f0ec0a
-- title:
--   Native arbitrary-child execution in at most 181nq+10T transitions with the computed precision retained
-- statement:
--   For positive n,b and q=b+3 lg(n)+5, suppose any finite child machine M halts on the Fourier input at precision q after T transitions with canonical binary output w. The constructed wrapper starts from the ordinary requested input and halts with exactly w on native output within 181nq+10T transitions. Its output head is at |w|+1, and the exact full final configuration is specified. All preprocessing, input preparation, child execution, cleanup, output shifting, and handoffs are charged. No regularity of a runtime function is assumed. In addition, the returned arithmetic word v is certified to have value q, the guard precision. This witness fact is preserved through the same machine execution and will be used to initialize the coordinate-scaling counter.
-- source:
--   Actual native I/O wrapper for an arbitrary Fourier child. This closes the input-rewriting and arbitrary-child invocation component; multiplier-based scaling and the normalized Fourier algorithm remain open components of the root theorem.

import Definitions.Def_BitDFT_NativeChildOutput
open BitDFT.NativeChildOutput BitDFT IntMul MachineSequence

theorem BitDFT.native_child_output_with_precision (M : MultitapeTM) (n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) (U : Fin n → ℤ × ℤ)
    (T : ℕ)
    (halt : (M.step^[T] (M.initCfg (fourierInput (guardPrecision n b) U) [])).state = M.qHalt)
    (w : List Bool)
    (out : (M.step^[T] (M.initCfg (fourierInput (guardPrecision n b) U) [])).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    let q := guardPrecision n b
    let x := fourierInput q U
    ∃ t v, t ≤ 181*n*q+10*T ∧ BinaryCounter.value v = q ∧
      (program M).step^[t] ((program M).initCfg (requestedInput b U) []) =
        final M (ChildCall.final M
          (CallerReady.final (ChildCall.child M) M.k (RewriteInput.final n b (encVector (q+1) U) v) x) x T w) w ∧
      (program M).HaltsWithOutput (requestedInput b U) [] t w ∧
      ((program M).step^[t] ((program M).initCfg (requestedInput b U) [])).head (program M).outTape = w.length+1 := by sorry
