-- Prove2me | Theorems.Thm_BitDFT_scalar_magnitude_branch
-- name    : BitDFT.scalar_magnitude_branch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T17:59:20.011605+00:00
-- url     : https://prove2.me/theorems/44400e9b-d24b-40b3-a94b-62a1b7a9e462
-- title:
--   The leading magnitude bit selects a fixed-width multiplication or exact power-of-two shift
-- statement:
--   For a natural magnitude a at most 2^q, its (q+1)-bit encoding either starts with zero and has the q-bit encoding of a as its tail, or a equals 2^q and the encoding is one followed by q zeros. In the latter case multiplying by n gives n times 2^q. This identifies the exact branch needed to call an arbitrary multiplication algorithm at width q only.
-- source:
--   Exact coordinate scaling for the integer multiplication to finite-precision DFT mission.

import Definitions.Def_BitDFT_Numerics
open BitDFT IntMul

theorem BitDFT.scalar_magnitude_branch (q a n : ℕ) (ha : a ≤ 2^q) :
    (a < 2^q ∧ bin (q+1) a = false :: bin q a) ∨
    (a = 2^q ∧ bin (q+1) a = true :: List.replicate q false ∧
      n*a = n*2^q) := by sorry
