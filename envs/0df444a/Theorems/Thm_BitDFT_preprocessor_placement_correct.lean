-- Prove2me | Theorems.Thm_BitDFT_preprocessor_placement_correct
-- name    : BitDFT.preprocessor_placement_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T17:12:44.675544+00:00
-- url     : https://prove2.me/theorems/8c7b3ba5-4fb8-44a2-9152-199efe105b32
-- title:
--   Native 27nq preprocessing with exact output heads and fresh child banks
-- statement:
--   For positive n and b, q=b+3 lg(n)+5, and every encoded input vector U, the routed machine starts from ordinary native input and halts within 27nq transitions with the rewritten Fourier input. Its output head is immediately after that word. Every reserved child bank is exactly blank after its permanent marker, and every child-bank head remains at zero. The conclusion additionally identifies the complete final configuration through the original preprocessor embedding.
-- source:
--   Strengthens the native preprocessing result with the physical tape and head layout needed for a genuine arbitrary-machine call. The complete transfer theorem remains open.

import Definitions.Def_BitDFT_PreprocessorPlacement
open BitDFT.PreprocessorPlacement BitDFT IntMul

theorem BitDFT.preprocessor_placement_correct (N : MultitapeTM) (r n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) (U : Fin n → ℤ × ℤ) :
    let q := guardPrecision n b
    let P := machine N r
    ∃ t v, t ≤ 27*n*q ∧
      P.step^[t] (P.initCfg (requestedInput b U) []) = embed N r (RewriteInput.final n b (encVector (q+1) U) v) ∧
      (P.step^[t] (P.initCfg (requestedInput b U) [])).state = P.qHalt ∧
      (P.step^[t] (P.initCfg (requestedInput b U) [])).cells P.outTape = P.tapeOf ((fourierInput q U).map P.bitSym) ∧
      (P.step^[t] (P.initCfg (requestedInput b U) [])).head P.outTape = (fourierInput q U).length+1 ∧
      (∀ i : Fin P.k, 2 ≤ i.val → i.val < r+2 →
        (P.step^[t] (P.initCfg (requestedInput b U) [])).cells i = N.tapeOf [] ∧
        (P.step^[t] (P.initCfg (requestedInput b U) [])).head i = 0) := by sorry
