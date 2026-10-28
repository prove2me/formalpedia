-- Prove2me | Theorems.Thm_BitDFT_guard_log_from_size
-- name    : BitDFT.guard_log_from_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:53:00.247396+00:00
-- url     : https://prove2.me/theorems/5515dba7-e330-4915-9711-06535e4ff50c
-- title:
--   Compute the guarded ceiling logarithm from binary length and a power-of-two flag
-- statement:
--   For every positive integer n, let k be the length of its canonical binary representation. Then lg(n), defined as max(ceil(log₂ n),1), equals max(k−1,1) when n=2^(k−1), and equals k otherwise. Thus the value needed by the precision wrapper is determined by the binary field length and whether its bits represent a power of two. This is an arithmetic identity, not a runtime claim for the flag-computing machine.
-- source:
--   Derived from the existing Mathlib binary-size characterization and the Galois connection between ceiling logarithms and exponentiation. Used to specify the logarithmic increment prepared for the BitDFT binary counter.

import Definitions.Def_IntMul_MultitapeModel

theorem BitDFT.guard_log_from_size (n : ℕ) (hn : 1 ≤ n) :
    IntMul.lg n = max (if n = 2^(n.size-1) then n.size-1 else n.size) 1 := by sorry
