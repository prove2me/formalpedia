-- Prove2me | solution 86 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:12:33.20881+00:00
-- url     : https://prove2.me/submissions/b77537f6-406b-4472-8c6f-055fa7cbaebe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_MasulloRH_quadratic_mertens_prefix_bounds
import Theorems.Thm_MasulloRH_mertens_energy_criterion_and_critical_divergence

theorem solution : RiemannHypothesis :=
  by
  obtain ⟨-, h2, -, -⟩ := MasulloRH.mertens_energy_criterion_and_critical_divergence
  exact h2.mpr MasulloRH.quadratic_mertens_prefix_bounds
