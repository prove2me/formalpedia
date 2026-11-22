-- Prove2me | solution 2 for riemannZeta_eq_zero_re
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @LG
-- created : 2026-11-21T16:13:34.933716+00:00
-- url     : https://prove2.me/submissions/81fee65a-510c-4ae5-90d3-1c95e2b9c206
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_riemannZeta_zero_nontrivial_in_critical_strip
import Theorems.Thm_AlpoGeChallenge_LFunction_eq_zero_re_of_isPrimitive
import Mathlib

open scoped DirichletCharacter

theorem solution :
    ∀ s : ℂ, riemannZeta s = 0 →
      (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2 := by
  intro s hz h_nontrivial _hs_ne_one
  obtain ⟨h_pos, h_lt_one⟩ :=
    GRH.riemannZeta_zero_nontrivial_in_critical_strip hz h_nontrivial
  have h_primitive : (1 : DirichletCharacter ℂ 1).IsPrimitive :=
    DirichletCharacter.isPrimitive_one_level_one
  have hL : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s = 0 := by
    simpa using hz
  exact AlpoGeChallenge.LFunction_eq_zero_re_of_isPrimitive 1
    (1 : DirichletCharacter ℂ 1) h_primitive s h_pos h_lt_one hL
