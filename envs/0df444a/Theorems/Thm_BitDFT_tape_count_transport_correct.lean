-- Prove2me | Theorems.Thm_BitDFT_tape_count_transport_correct
-- name    : BitDFT.tape_count_transport_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T18:26:44.433986+00:00
-- url     : https://prove2.me/theorems/40694d71-7599-40c0-8c9a-2d624aeb0510
-- title:
--   Transporting equal tape counts preserves every machine step exactly
-- statement:
--   For every starting configuration and natural step count t, transporting the tape-count type before running t transitions gives exactly the transport of the original machine run. There is no runtime overhead. This applies when two composition stages express the same finite tape count using different arithmetic expressions.
-- source:
--   Type-correct composition of child-wrapper and scaler tape layouts.

import Definitions.Def_BitDFT_TapeCountTransport
open BitDFT.TapeCountTransport IntMul

theorem BitDFT.tape_count_transport_correct (M : MultitapeTM) (n : ℕ) (h : M.k = n) (c : M.Cfg) (t : ℕ) :
    (machine M n h).step^[t] (embed M n h c) = embed M n h (M.step^[t] c) := by sorry
