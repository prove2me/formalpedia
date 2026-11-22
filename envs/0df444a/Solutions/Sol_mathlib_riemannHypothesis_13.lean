-- Prove2me | solution 13 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:26:04.180811+00:00
-- url     : https://prove2.me/submissions/32d2a092-0265-4449-9127-91c85f95b8c3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_moebius_dirichlet_series_holomorphic_extension
import Theorems.Thm_riemann_hypothesis_iff_moebius_holomorphic_extension

theorem solution : RiemannHypothesis :=
  riemann_hypothesis_iff_moebius_holomorphic_extension.mpr
    moebius_dirichlet_series_holomorphic_extension
