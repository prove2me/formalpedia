-- Prove2me | Theorems.Thm_BitDFT_child_retained_precision
-- name    : BitDFT.child_retained_precision
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T18:07:07.018355+00:00
-- url     : https://prove2.me/theorems/d270d5d6-9efa-4aa1-b41e-13168aa1fb90
-- title:
--   Canonical precision survives the arbitrary child call and native output return
-- statement:
--   In the specified final configuration of the complete child-call wrapper, the original preprocessor precision word remains on tape k+3, where k is the child machine tape count. This tape contains the canonical binary representation of the guard precision q, with its head at q.size+1. The assertion holds for any child machine and the full parameterized final configuration. The separately proved wrapper execution theorem supplies reachability and its charged clock; this lemma identifies the workspace available to the subsequent scaler.
-- source:
--   Exact configuration bridge from arbitrary child invocation to descriptor initialization in the DFT output scaler.

import Definitions.Def_BitDFT_NativeChildOutput
open BitDFT IntMul

theorem BitDFT.child_retained_precision (M : MultitapeTM) (n b : ℕ) (rest v x w : List Bool) (T : ℕ)
    (hv : BinaryCounter.value v = guardPrecision n b) :
    let i : Fin (NativeChildOutput.program M).k := ⟨3+M.k,by change 3+M.k < 5+M.k; omega⟩
    let result := NativeChildOutput.final M
      (ChildCall.final M (CallerReady.final (ChildCall.child M) M.k
        (RewriteInput.final n b rest v) x) x T w) w
    result.cells i = (NativeChildOutput.program M).tapeOf
      ((bin (guardPrecision n b).size (guardPrecision n b)).map (NativeChildOutput.program M).bitSym) ∧
    result.head i = (guardPrecision n b).size+1 := by sorry
