-- Prove2me | Theorems.Thm_BitDFT_preprocessor_alphabet_correct
-- name    : BitDFT.preprocessor_alphabet_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:56:41.343451+00:00
-- url     : https://prove2.me/theorems/a82557b6-6cf4-4552-ad05-acd9873d02a0
-- title:
--   The 27nq preprocessing bound holds over any target alphabet
-- statement:
--   For any target multitape machine N, n,b≥1, and integer-pair vector U of length n, the adapted fixed preprocessor computes exactly fourierInput(q,U) from requestedInput(b,U) within 27nq transitions, where q=b+3 max(ceil(log₂ n),1)+5. It uses N’s alphabet and preserves the original preprocessor’s five tapes and runtime. This is alphabet compatibility only; buffer placement and invocation of N are separate operations.
-- source:
--   Reuses the exact native preprocessing theorem and constructed injective alphabet adapter; no monotonicity or smoothness assumption on any runtime function is used.

import Definitions.Def_BitDFT_PreprocessorAlphabet
open BitDFT IntMul

theorem BitDFT.preprocessor_alphabet_correct (N : MultitapeTM) (n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) (U : Fin n → ℤ × ℤ) :
    Computes (PreprocessorAlphabet.machine N) (requestedInput b U) (fourierInput (guardPrecision n b) U)
      (27 * (n : ℝ) * (guardPrecision n b : ℝ)) := by sorry
