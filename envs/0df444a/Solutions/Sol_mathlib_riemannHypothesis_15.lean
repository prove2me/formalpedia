-- Prove2me | solution 15 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:26:06.188166+00:00
-- url     : https://prove2.me/submissions/692fdab6-49a3-4eff-af23-2bf4ebefda0a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_BroughanRH_weil
import Theorems.Thm_ConnesRZFrontier_weilPositive_iff_mathlib_RH

theorem solution : RiemannHypothesis :=
  ConnesRZFrontier.weilPositive_iff_mathlib_RH.mp BroughanRH.weil
