-- Prove2me | solution 24 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:33:27.896769+00:00
-- url     : https://prove2.me/submissions/d49321b9-08c7-4808-8071-f0899c6848ce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_connes_spectral_rh
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

theorem solution : RiemannHypothesis :=
  riemannHypothesis_iff_zeros_in_strip_on_line.mpr (fun s hz h0 h1 => connes_spectral_rh s h0 h1 hz)
