-- Prove2me | solution 1 for zeta_ne_zero_of_strip_of_two_lt_abs_im
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-20T22:36:29.16482+00:00
-- url     : https://prove2.me/submissions/9944c166-73d1-49cd-9693-ffddf99e90c9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AlpoGeChallenge_LFunction_eq_zero_re_of_isPrimitive
import Theorems.Thm_GRH_grh_critical_line_iff

open Complex

theorem solution (s : ℂ) (h0 : 1 / 2 < s.re) (h1 : s.re < 1)
    (him : 2 < |s.im|) : riemannZeta s ≠ 0 := by
  have hs1 : s ≠ 1 := fun h => by simp [h] at h1
  have h := GRH.grh_critical_line_iff.mp AlpoGeChallenge.LFunction_eq_zero_re_of_isPrimitive
    1 (1 : DirichletCharacter ℂ 1) s h0 (fun h => hs1 h.2)
  rwa [DirichletCharacter.LFunction_modOne_eq] at h
