-- Prove2me | solution 22 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:30:25.676636+00:00
-- url     : https://prove2.me/submissions/a3381e98-a996-4839-bf6a-7a85b700c13d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_rhOfAll

theorem solution : RiemannHypothesis :=
  fun s hz htriv hone => rhOfAll s hz htriv hone
