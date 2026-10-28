-- Prove2me | Theorems.Thm_BitDFT_child_descriptor_output
-- name    : BitDFT.child_descriptor_output
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T18:36:51.189831+00:00
-- url     : https://prove2.me/theorems/ad41538f-9b5b-4b4b-8c70-c4c84ca0aa92
-- title:
--   Child execution and descriptor setup preserve the exact native output and its ending head
-- statement:
--   Let n and b be positive, q the guard precision, and suppose an arbitrary child machine computes output word w from the Fourier input at precision q in T transitions. The combined machine starts from the original requested input and reaches its specified complete final configuration within 190 n q + 10 T transitions. The final configuration is the child-wrapper output followed by preparation of the two descriptor tapes containing the canonical binary word for q. The returned arithmetic witness is certified to have value q. Input rewriting, child invocation, output return, tape-head rewind, descriptor copying, and the controller handoff are all included in the bound. The combined machine also halts with exactly the child output word w on its native output tape and leaves that tape head at |w|+1. These conclusions permit a subsequent charged rewind before coordinate extraction.
-- source:
--   Actual-machine composition for output-scaler initialization; coordinate scaling and the normalized DFT machine remain separate obligations.

import Definitions.Def_BitDFT_ChildDescriptor
open BitDFT.ChildDescriptor BitDFT IntMul MachineSequence

theorem BitDFT.child_descriptor_output (M : MultitapeTM) (n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) (U : Fin n → ℤ × ℤ)
    (T : ℕ)
    (halt : (M.step^[T] (M.initCfg (fourierInput (guardPrecision n b) U) [])).state = M.qHalt)
    (w : List Bool)
    (out : (M.step^[T] (M.initCfg (fourierInput (guardPrecision n b) U) [])).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    let q := guardPrecision n b
    let x := fourierInput q U
    ∃ t v, t ≤ 190*n*q+10*T ∧ BinaryCounter.value v = q ∧
      (machine M).step^[t] ((machine M).initCfg (requestedInput b U) []) =
        final M (requestedInput b U)
          (NativeChildOutput.final M (ChildCall.final M
            (CallerReady.final (ChildCall.child M) M.k (RewriteInput.final n b (encVector (q+1) U) v) x) x T w) w)
          (bin q.size q) ∧
      (machine M).HaltsWithOutput (requestedInput b U) [] t w ∧
      ((machine M).step^[t] ((machine M).initCfg (requestedInput b U) [])).head (machine M).outTape = w.length+1 := by sorry
