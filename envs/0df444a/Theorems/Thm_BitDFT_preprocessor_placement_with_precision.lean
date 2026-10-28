-- Prove2me | Theorems.Thm_BitDFT_preprocessor_placement_with_precision
-- name    : BitDFT.preprocessor_placement_with_precision
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T18:25:23.187993+00:00
-- url     : https://prove2.me/theorems/bf5c2817-a5da-42a5-a76b-201944385006
-- title:
--   Native 27nq preprocessing with exact output heads and fresh child banks with the computed precision retained
-- statement:
--   For positive n and b, q=b+3 lg(n)+5, and every encoded input vector U, the routed machine starts from ordinary native input and halts within 27nq transitions with the rewritten Fourier input. Its output head is immediately after that word. Every reserved child bank is exactly blank after its permanent marker, and every child-bank head remains at zero. The conclusion additionally identifies the complete final configuration through the original preprocessor embedding. In addition, the returned arithmetic word v is certified to have value q, the guard precision. This witness fact is preserved through the same machine execution and will be used to initialize the coordinate-scaling counter.
-- source:
--   Strengthens the native preprocessing result with the physical tape and head layout needed for a genuine arbitrary-machine call. The complete transfer theorem remains open.

import Definitions.Def_BitDFT_PreprocessorPlacement
open BitDFT.PreprocessorPlacement BitDFT IntMul

theorem BitDFT.preprocessor_placement_with_precision (N : MultitapeTM) (r n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) (U : Fin n → ℤ × ℤ) :
    let q := guardPrecision n b
    let P := machine N r
    ∃ t v, t ≤ 27*n*q ∧ BinaryCounter.value v = q ∧
      P.step^[t] (P.initCfg (requestedInput b U) []) = embed N r (RewriteInput.final n b (encVector (q+1) U) v) ∧
      (P.step^[t] (P.initCfg (requestedInput b U) [])).state = P.qHalt ∧
      (P.step^[t] (P.initCfg (requestedInput b U) [])).cells P.outTape = P.tapeOf ((fourierInput q U).map P.bitSym) ∧
      (P.step^[t] (P.initCfg (requestedInput b U) [])).head P.outTape = (fourierInput q U).length+1 ∧
      (∀ i : Fin P.k, 2 ≤ i.val → i.val < r+2 →
        (P.step^[t] (P.initCfg (requestedInput b U) [])).cells i = N.tapeOf [] ∧
        (P.step^[t] (P.initCfg (requestedInput b U) [])).head i = 0) := by sorry
