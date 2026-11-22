-- Prove2me | solution 29 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:29:35.573147+00:00
-- url     : https://prove2.me/submissions/24bba59e-7df5-4668-8b7a-21745136bf12
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_GRH_grh_critical_line_iff
import Theorems.Thm_OAI_ShortDraftMellin_dirichlet_exp_zero_free_of_power_bound_only
import Theorems.Thm_OAI_ShortDraftMellin_principal_dirichlet_exp_zero_free_of_power_bound_only
import Theorems.Thm_GRH_smoothed_mobius_character_power_bound
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

-- Step 1: `GRH.smoothed_mobius_character_power_bound` implies `AlpoGeChallenge.LFunction_eq_zero_re_of_isPrimitive` (accepted reduction of `AlpoGeChallenge.LFunction_eq_zero_re_of_isPrimitive`).
section

open OAI.ShortDraftMellin

theorem AlpoGeChallenge.LFunction_eq_zero_re_of_isPrimitive :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 →
        s.re = 1 / 2 := by
  apply GRH.grh_critical_line_iff.mpr
  intro q _ χ s hs hpole
  obtain ⟨σ, hhalf, hmin⟩ :=
    exists_between (lt_min (by norm_num : (1 / 2 : ℝ) < 1) hs)
  have hone : σ < 1 := lt_of_lt_of_le hmin (min_le_left _ _)
  have hreal : σ < s.re := lt_of_lt_of_le hmin (min_le_right _ _)
  have hpos : 0 < σ := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hhalf
  have hbound := GRH.smoothed_mobius_character_power_bound q χ σ hhalf hone
  by_cases hχ : χ = 1
  · subst χ
    exact principal_dirichlet_exp_zero_free_of_power_bound_only q σ hpos hone
      hbound s hreal (fun heq => hpole ⟨rfl, heq⟩)
  · exact dirichlet_exp_zero_free_of_power_bound_only χ hχ σ hpos hone
      hbound s hreal

end

-- Step 2: `AlpoGeChallenge.LFunction_eq_zero_re_of_isPrimitive` implies `RiemannHypothesis` (accepted reduction of `mathlib_riemannHypothesis`).
section

theorem solution : RiemannHypothesis := by
  refine riemannHypothesis_iff_zeros_in_strip_on_line.mpr (fun s hz h0 h1 => ?_)
  rw [← DirichletCharacter.LFunction_modOne_eq (χ := (1 : DirichletCharacter ℂ 1))] at hz
  exact AlpoGeChallenge.LFunction_eq_zero_re_of_isPrimitive 1 1 DirichletCharacter.isPrimitive_one_level_one s h0 h1 hz

end
