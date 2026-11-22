-- Prove2me | solution 20 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:26:10.676428+00:00
-- url     : https://prove2.me/submissions/fe9afc80-b4a4-4f3a-8634-42f6048d18e2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_MasulloRH_finite_square_prime_energy_cap
import Theorems.Thm_MasulloRH_riemannHypothesis_iff_square_sampled_prime_energy

theorem solution : RiemannHypothesis :=
  by
  obtain ⟨-, h2, -⟩ := MasulloRH.riemannHypothesis_iff_square_sampled_prime_energy
  exact h2.mpr (fun N => MasulloRH.finite_square_prime_energy_cap N)
