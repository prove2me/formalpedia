-- Prove2me | Theorems.Thm_BitDFT_child_call_with_precision
-- name    : BitDFT.child_call_with_precision
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T18:26:13.155979+00:00
-- url     : https://prove2.me/theorems/8e1d91a9-907c-4f42-adf7-8e3d55ed7fea
-- title:
--   Call any Fourier child from the native request within 176nq+6T transitions with the computed precision retained
-- statement:
--   Let n,b be positive, q=b+3 lg(n)+5, and x the Fourier input at precision q. If an arbitrary finite machine M halts on x with binary output w after T transitions, the constructed caller starts from the ordinary requested input and reaches the exact returned-buffer configuration within 176nq+6T transitions. All preprocessing, copies, markers, head placement, child execution, return, cleanup, and handoffs are charged. No monotonicity or other regularity of a runtime function is used. The returned word still needs the separate native-output shift. In addition, the returned arithmetic word v is certified to have value q, the guard precision. This witness fact is preserved through the same machine execution and will be used to initialize the coordinate-scaling counter.
-- source:
--   Actual native-request to arbitrary-child returned-buffer theorem. This is a component of the full integer multiplication to DFT theorem, not the full theorem.

import Definitions.Def_BitDFT_ChildCall
open BitDFT.ChildCall BitDFT IntMul MachineSequence
open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankedSimulation (extents)
open IntMul.TrackedBankPreparation (inputWord initialExtent)

theorem BitDFT.child_call_with_precision (M : MultitapeTM) (n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) (U : Fin n → ℤ × ℤ)
    (T : ℕ)
    (halt : (M.step^[T] (M.initCfg (fourierInput (guardPrecision n b) U) [])).state = M.qHalt)
    (w : List Bool)
    (out : (M.step^[T] (M.initCfg (fourierInput (guardPrecision n b) U) [])).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    let q := guardPrecision n b
    let x := fourierInput q U
    ∃ t v, t ≤ 176*n*q+6*T ∧ BinaryCounter.value v = q ∧
      (program M).step^[t] ((program M).initCfg (requestedInput b U) []) =
        final M (CallerReady.final (child M) M.k (RewriteInput.final n b (encVector (q+1) U) v) x) x T w := by sorry
