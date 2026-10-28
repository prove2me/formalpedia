-- Prove2me | Theorems.Thm_BitDFT_caller_ready_with_precision
-- name    : BitDFT.caller_ready_with_precision
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T18:26:01.509807+00:00
-- url     : https://prove2.me/theorems/239b472e-755a-4ecb-a72c-9700b5969a12
-- title:
--   Reach the child-call buffer and bank-head layout within 71nq native transitions with the computed precision retained
-- statement:
--   For positive n,b and q=b+3 lg(n)+5, the fixed preparation machine starts from the ordinary encoded request and reaches its exact final configuration in at most 71nq transitions. Its output tape holds a blank gap followed by the rewritten Fourier input and a separator, with the output head at cell 1. Every reserved child-bank tape is blank after its permanent marker, and every reserved head is physically at cell 1. No input normalization, copying, bank allocation, head positioning, or handoff is free. In addition, the returned arithmetic word v is certified to have value q, the guard precision. This witness fact is preserved through the same machine execution and will be used to initialize the coordinate-scaling counter.
-- source:
--   Actual native preparation for the integer multiplication to finite-precision DFT transfer. The child execution, return path, multiplier-based scaling, and normalized Fourier machine remain to be composed and verified.

import Definitions.Def_BitDFT_CallerReady
open BitDFT.CallerReady BitDFT IntMul MachineSequence

theorem BitDFT.caller_ready_with_precision (N : MultitapeTM) (r n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) (U : Fin n → ℤ × ℤ) :
    let q := guardPrecision n b
    let w := fourierInput q U
    ∃ t v, t ≤ 71*n*q ∧ BinaryCounter.value v = q ∧
      (machine N r).step^[t] ((machine N r).initCfg (requestedInput b U) []) =
        final N r (RewriteInput.final n b (encVector (q+1) U) v) w ∧
      (final N r (RewriteInput.final n b (encVector (q+1) U) v) w).cells (machine N r).outTape =
        (machine N r).tapeOf ([(machine N r).blank]++w.map (machine N r).bitSym++[(machine N r).sep]) ∧
      (final N r (RewriteInput.final n b (encVector (q+1) U) v) w).head (machine N r).outTape = 1 ∧
      (∀ i : Fin (machine N r).k, 2 ≤ i.val → i.val < r+2 →
        (final N r (RewriteInput.final n b (encVector (q+1) U) v) w).cells i = N.tapeOf [] ∧
        (final N r (RewriteInput.final n b (encVector (q+1) U) v) w).head i = 1) := by sorry
