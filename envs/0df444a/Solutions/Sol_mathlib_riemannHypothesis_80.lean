-- Prove2me | solution 80 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:32:48.935246+00:00
-- url     : https://prove2.me/submissions/4a73140c-7245-479d-95b0-9ce9382690a3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_TowardsGRH_LW56e2_b83dbbd_dirichlet_zero_free_bound
import Theorems.Thm_AlpoegeClaudeRH_EveryCharacter_below_record
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

-- Step 1: `AlpoegeClaudeRH.EveryCharacter_below_record` implies `AlpoegeClaudeRH.EveryCharacter` (accepted reduction of `AlpoegeClaudeRH.EveryCharacter`).
section

/-- Proof sketch for `AlpoegeClaudeRH.EveryCharacter`.

    Split the half-plane `Re(s) > 1/2` at the verified zero-free boundary
    `0.8749570698`. Above the boundary nonvanishing is already Proved; at or
    below it we invoke the strictly weaker child carrying
    `hcap : s.re ≤ 0.8749570698`.

    The target states the pole exclusion as `χ ≠ 1 ∨ s ≠ 1` while the record
    theorem states it as `¬ (χ = 1 ∧ s = 1)`; the two are interconverted by
    De Morgan's laws (`tauto`), which is pure propositional logic. -/
theorem AlpoegeClaudeRH.EveryCharacter (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ)
    (hs : 1 / 2 < s.re) (h : χ ≠ 1 ∨ s ≠ 1) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  by_cases hrec : (0.8749570698 : ℝ) < s.re
  · -- Above the boundary: the audited uniform zero-free record.
    exact TowardsGRH_LW56e2_b83dbbd.dirichlet_zero_free_bound χ hrec (by tauto)
  · -- At or below the boundary: the remaining open child.
    exact AlpoegeClaudeRH.EveryCharacter_below_record N χ s hs h (le_of_not_gt hrec)

end

-- Step 2: `AlpoegeClaudeRH.EveryCharacter` implies `RiemannHypothesis` (accepted reduction of `mathlib_riemannHypothesis`).
section

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

end
