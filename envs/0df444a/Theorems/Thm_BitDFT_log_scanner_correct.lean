-- Prove2me | Theorems.Thm_BitDFT_log_scanner_correct
-- name    : BitDFT.log_scanner_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:09:39.258129+00:00
-- url     : https://prove2.me/theorems/9ecd9597-1ef3-488d-9b05-ef6eba2ba9ec
-- title:
--   The finite logarithmic scanner prepares exactly 3 lg(n)+5 unary marks
-- statement:
--   Let n be the positive integer represented by a binary word consisting of a leading one followed by an arbitrary tail. Set K=3 max(ceil(log₂ n),1)+5. From the prepared work-tape configuration, the explicit finite scanner halts after exactly K+3 transitions. Its unary work tape contains exactly K marks with its head on the final mark. The dimension word remains unchanged, its head is just after the word, and all native input/output data and head positions are preserved. This supplies the unary operand needed by the guard-precision counter; it is not yet a complete request-header rewrite.
-- source:
--   Combines exact finite-machine scan and padding invariants with the proved BitDFT.guard_log_from_size identity. A direct binary-value argument shows that a leading-one word has its expected binary length and is a power of two exactly when all tail bits are zero.

import Definitions.Def_BitDFT_LogScanner
open BitDFT.LogScanner IntMul

theorem BitDFT.log_scanner_correct (base : machine.Cfg) (tail : List Bool) :
    let k := 3*IntMul.lg (IntMul.val (true::tail))+5
    machine.step^[k+3] (frame base .start (true::tail) 1 0 1) =
      frame base .halt (true::tail) (tail.length+2) k k := by sorry
