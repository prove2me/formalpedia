-- Prove2me | Theorems.Thm_BitDFT_encoded_precision_correct
-- name    : BitDFT.encoded_precision_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:15:33.341979+00:00
-- url     : https://prove2.me/theorems/b6fc588b-9e05-49d4-9dca-2609ce389463
-- title:
--   Compute guard precision from the actual integer encoding in at most 11q transitions
-- statement:
--   For every n,b≥1 and arbitrary binary suffix r, set q=b+3 max(ceil(log₂ n),1)+5. The same fixed five-tape machine, starting from ordinary native input encNat(n)encNat(b)r, halts within 11q transitions. It holds a little-endian word of value q and length at most q on its precision work tape, retains the canonical dimension word, clears the unary workspace, and preserves the native input with its head at r. The complete final configuration is specified. This computes the precision internally; serialization of a rewritten request is a subsequent stage.
-- source:
--   Specializes the actual native-input precision machine to the mission encoding. Proves binary decoding and the canonical leading bit, then absorbs the explicit parsing/setup lengths into 11q without an assumed parser or free work-tape initialization.

import Definitions.Def_BitDFT_NativePrecision
import Definitions.Def_BitDFT_Numerics
open BitDFT IntMul BitDFT.NativePrecision

theorem BitDFT.encoded_precision_correct (n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) (rest : List Bool) :
    let q := guardPrecision n b
    let x := encNat n ++ encNat b ++ rest
    ∃ t v, t ≤ 11*q ∧ BinaryCounter.value v = q ∧ v.length ≤ q ∧
      machine.step^[t] (machine.initCfg x []) =
        final x (bin n.size n).tail (bin b.size b) v := by sorry
