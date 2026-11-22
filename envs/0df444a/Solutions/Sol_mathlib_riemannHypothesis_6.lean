-- Prove2me | solution 6 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:19:31.003541+00:00
-- url     : https://prove2.me/submissions/debcfcc8-f136-4c4d-900a-4adddf71a51f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AlpoGeChallenge_LFunction_eq_zero_re_of_isPrimitive
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

theorem solution : RiemannHypothesis := by
  refine riemannHypothesis_iff_zeros_in_strip_on_line.mpr (fun s hz h0 h1 => ?_)
  rw [← DirichletCharacter.LFunction_modOne_eq (χ := (1 : DirichletCharacter ℂ 1))] at hz
  exact AlpoGeChallenge.LFunction_eq_zero_re_of_isPrimitive 1 1 DirichletCharacter.isPrimitive_one_level_one s h0 h1 hz
