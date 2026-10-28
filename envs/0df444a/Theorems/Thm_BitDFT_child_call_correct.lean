-- Prove2me | Theorems.Thm_BitDFT_child_call_correct
-- name    : BitDFT.child_call_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T17:32:20.311291+00:00
-- url     : https://prove2.me/theorems/328a69b9-aa91-4675-89ec-7db49713107d
-- title:
--   Call any Fourier child from the native request within 176nq+6T transitions
-- statement:
--   Let n,b be positive, q=b+3 lg(n)+5, and x the Fourier input at precision q. If an arbitrary finite machine M halts on x with binary output w after T transitions, the constructed caller starts from the ordinary requested input and reaches the exact returned-buffer configuration within 176nq+6T transitions. All preprocessing, copies, markers, head placement, child execution, return, cleanup, and handoffs are charged. No monotonicity or other regularity of a runtime function is used. The returned word still needs the separate native-output shift.
-- source:
--   Actual native-request to arbitrary-child returned-buffer theorem. This is a component of the full integer multiplication to DFT theorem, not the full theorem.

import Definitions.Def_BitDFT_ChildCall
open BitDFT.ChildCall BitDFT IntMul MachineSequence
open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankedSimulation (extents)
open IntMul.TrackedBankPreparation (inputWord initialExtent)

theorem BitDFT.child_call_correct (M : MultitapeTM) (n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) (U : Fin n → ℤ × ℤ)
    (T : ℕ)
    (halt : (M.step^[T] (M.initCfg (fourierInput (guardPrecision n b) U) [])).state = M.qHalt)
    (w : List Bool)
    (out : (M.step^[T] (M.initCfg (fourierInput (guardPrecision n b) U) [])).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    let q := guardPrecision n b
    let x := fourierInput q U
    ∃ t v, t ≤ 176*n*q+6*T ∧
      (program M).step^[t] ((program M).initCfg (requestedInput b U) []) =
        final M (CallerReady.final (child M) M.k (RewriteInput.final n b (encVector (q+1) U) v) x) x T w := by sorry
