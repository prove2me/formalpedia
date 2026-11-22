-- Prove2me | solution 14 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:26:05.151124+00:00
-- url     : https://prove2.me/submissions/aa8374c1-658d-42ed-b39e-b31b7687f533
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_BroughanRH_landau
import Theorems.Thm_LandauFunction_landau_riemann_hypothesis_iff

theorem solution : RiemannHypothesis :=
  LandauFunction.landau_riemann_hypothesis_iff.mp BroughanRH.landau
