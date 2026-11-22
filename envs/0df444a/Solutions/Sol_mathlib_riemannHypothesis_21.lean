-- Prove2me | solution 21 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:26:11.412504+00:00
-- url     : https://prove2.me/submissions/e130ac93-1db9-4274-badb-66c277b5e2d6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_GRH_reduced_liouville_harmonic_power_decay
import Theorems.Thm_GRH_riemannHypothesis_iff_harmonic_liouville_decay_at_fixed_modulus

theorem solution : RiemannHypothesis :=
  (GRH.riemannHypothesis_iff_harmonic_liouville_decay_at_fixed_modulus 1).mpr
    (fun σ h1 h2 => GRH.reduced_liouville_harmonic_power_decay 1 σ h1 h2)
