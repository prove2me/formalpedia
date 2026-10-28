-- Prove2me | Theorems.Thm_BitDFT_buffer_shift_correct
-- name    : BitDFT.buffer_shift_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T17:02:06.803885+00:00
-- url     : https://prove2.me/theorems/fd6382d3-016d-49d7-8abf-f005bc89f066
-- title:
--   Prepare a child input buffer in exactly 3|w|+5 transitions
-- statement:
--   For every binary word w and arbitrary native-input configuration, starting with w on the output tape and its head just beyond w, the fixed buffer-preparation machine halts after exactly 3|w|+5 transitions. Its complete final output tape contains a blank gap, then w, then a separator, followed by blanks; its output head is at the gap. The native input tape and its head are preserved. This includes the empty-word case.
-- source:
--   Full-configuration, exact-clock machine lemma needed to place the rewritten Fourier input into the reusable tracked caller. This does not by itself implement the child call or the complete Fourier transfer.

import Definitions.Def_BitDFT_BufferShift
open BitDFT.BufferShift IntMul

theorem BitDFT.buffer_shift_correct (base : machine.Cfg) (w : List Bool) :
    machine.step^[3*w.length+5] (frame base .start (w.map machine.bitSym) (w.length+1)) =
      frame base .halt ([TapeCopy.Sym.blank]++w.map machine.bitSym++[TapeCopy.Sym.sep]) 1 := by sorry
