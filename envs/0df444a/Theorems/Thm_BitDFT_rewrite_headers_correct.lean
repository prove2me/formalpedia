-- Prove2me | Theorems.Thm_BitDFT_rewrite_headers_correct
-- name    : BitDFT.rewrite_headers_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:35:33.976116+00:00
-- url     : https://prove2.me/theorems/43a48012-fd32-4791-a631-aee8d4e427d2
-- title:
--   Rewrite native request headers within 19q actual transitions
-- statement:
--   For n,b≥1 and arbitrary binary suffix r, let q=b+3 max(ceil(log₂ n),1)+5. Starting from ordinary native input encNat(n)encNat(b)r, one fixed five-tape machine halts within 19q transitions in the specified full final configuration. Its output contains exactly encNat(n)encNat(q), and the native input is retained with its head at the suffix r. It parses the headers, computes q, removes high zero padding, serializes both rewritten headers, and performs all head positioning itself. The suffix has not yet been appended to output.
-- source:
--   Full native-input header rewriting stage for the integer-multiplication-to-DFT wrapper. It leaves suffix copying, the arbitrary Fourier-machine call, and multiplier-based output scaling as separate actual-machine obligations.

import Definitions.Def_BitDFT_RewriteHeaders
import Definitions.Def_BitDFT_Numerics
open BitDFT BitDFT.RewriteHeaders IntMul

theorem BitDFT.rewrite_headers_correct (n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) (rest : List Bool) :
    let q := guardPrecision n b
    let x := encNat n ++ encNat b ++ rest
    ∃ t v, t ≤ 19*q ∧ BinaryCounter.value v = q ∧ v.length ≤ q ∧
      machine.step^[t] (machine.initCfg x []) =
        final x (bin n.size n).tail (bin b.size b) v := by sorry
