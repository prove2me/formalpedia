-- Prove2me | Theorems.Thm_BitDFT_native_precision_correct
-- name    : BitDFT.native_precision_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:13:59.448326+00:00
-- url     : https://prove2.me/theorems/26f0bc4a-2b51-4ee4-aaa4-5bfdab6507c3
-- title:
--   Compute guard precision directly from native encoded headers
-- statement:
--   Let a canonical binary dimension word consist of a leading one and a tail a; let w represent positive b with |w|≤b. Write n for the dimension value, q=b+3 max(ceil(log₂ n),1)+5, and h(v)=1^{|v|}0v. On ordinary native input h(1a)h(w)r, one fixed five-tape machine halts with a little-endian word of value q and length at most q in at most 7q+3|a|+4|w|+18 transitions. It performs its own header parsing, work-tape preparation, and precision arithmetic; the full final configuration retains the dimension and native input suffix position. Rewriting the output header and computing the DFT remain separate stages.
-- source:
--   Actual native-input composition for the integer-multiplication-to-DFT transfer. Reuses accepted or independently compiled exact-machine components and verifies the complete handoff; this does not claim the complete Fourier transfer theorem.

import Definitions.Def_BitDFT_NativePrecision
import Definitions.Def_BitDFT_Numerics
open BitDFT BitDFT.NativePrecision IntMul

theorem BitDFT.native_precision_correct (tail w rest : List Bool) (hb : 1 ≤ IntMul.val w) (hw : w.length ≤ IntMul.val w) :
    let x := RequestHeaders.header (true::tail) ++ RequestHeaders.header w ++ rest
    let q := guardPrecision (IntMul.val (true::tail)) (IntMul.val w)
    ∃ t v, t ≤ 7*q+3*tail.length+4*w.length+18 ∧ BinaryCounter.value v = q ∧ v.length ≤ q ∧
      machine.step^[t] (machine.initCfg x []) = final x tail w v := by sorry
