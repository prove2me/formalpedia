-- Prove2me | solution 5 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:19:28.747807+00:00
-- url     : https://prove2.me/submissions/e72af0ff-dd70-4ee0-adef-df7bcb714918
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AlpoegeClaudeRH_EveryCharacter
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

theorem solution : RiemannHypothesis := by
  have hright : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → s ≠ 1 → riemannZeta s ≠ 0 := by
    intro s hs hs1
    have h := AlpoegeClaudeRH.EveryCharacter 1 (1 : DirichletCharacter ℂ 1) s hs (Or.inr hs1)
    rwa [DirichletCharacter.LFunction_modOne_eq] at h
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
