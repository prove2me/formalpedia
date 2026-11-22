-- Prove2me | solution 23 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:33:26.324011+00:00
-- url     : https://prove2.me/submissions/aa637f0a-b28c-4761-aa84-c7306cc82326
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Riemann_hypothesis__91a068
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

theorem solution : RiemannHypothesis :=
  riemannHypothesis_iff_zeros_in_strip_on_line.mpr (fun s hz h0 h1 => Riemann_hypothesis s h0 h1 hz)
