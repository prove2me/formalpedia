-- Prove2me | solution 3 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:19:25.687926+00:00
-- url     : https://prove2.me/submissions/31f083ff-4301-461c-ba7b-95291c39baaf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_MasulloRH_mission_riemann_hypothesis
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

theorem solution : RiemannHypothesis :=
  riemannHypothesis_iff_zeros_in_strip_on_line.mpr
    (fun s hz h0 h1 => MasulloRH.mission_riemann_hypothesis s h0 h1 hz)
