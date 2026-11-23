-- Prove2me | solution 87 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:29:03.625011+00:00
-- url     : https://prove2.me/submissions/5ecc7032-5ce1-4da4-b5d1-800222600bb2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AlpoGe_primitive_nonvanishing_below_record_of_row
import Theorems.Thm_AlpoGe_galoisLocalGlobalStrong_recParameter
import Theorems.Thm_TowardsGRH_LW56e2_b83dbbd_dirichlet_zero_free_bound
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

theorem solution : RiemannHypothesis := by
  -- No zero of zeta with Re s > 1/2 and s ≠ 1: the Proved record above the boundary,
  -- the Open child at modulus 1 at or below it.
  have hright : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → s ≠ 1 → riemannZeta s ≠ 0 := by
    intro s hs hs1
    have h : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s ≠ 0 := by
      by_cases hrec : (0.8749570698 : ℝ) < s.re
      · exact TowardsGRH_LW56e2_b83dbbd.dirichlet_zero_free_bound (q := 1)
          (1 : DirichletCharacter ℂ 1) hrec (fun h => hs1 h.2)
      · exact AlpoGe.primitive_nonvanishing_below_record_of_row
          AlpoGe.galoisLocalGlobalStrong_recParameter 1 (1 : DirichletCharacter ℂ 1)
          DirichletCharacter.isPrimitive_one_level_one s hs (le_of_not_gt hrec)
    rwa [DirichletCharacter.LFunction_modOne_eq] at h
  -- Reflection across the critical line by the functional equation.
  refine riemannHypothesis_iff_zeros_in_strip_on_line.mpr (fun s hz h0 h1 => ?_)
  have hs1 : s ≠ 1 := fun h => by rw [h] at h1; norm_num at h1
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · exfalso
    have hneg : ∀ n : ℕ, s ≠ -(n : ℂ) := fun n h => by
      have hre := congrArg Complex.re h
      simp at hre
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hfe := riemannZeta_one_sub hneg hs1
    rw [hz, mul_zero] at hfe
    have hre : (1 / 2 : ℝ) < (1 - s).re := by simp; linarith
    have h1s : (1 - s) ≠ 1 := fun h => by
      have hre' := congrArg Complex.re h
      simp at hre'
      linarith
    exact hright (1 - s) hre h1s hfe
  · exact heq
  · exact absurd hz (hright s hgt hs1)
