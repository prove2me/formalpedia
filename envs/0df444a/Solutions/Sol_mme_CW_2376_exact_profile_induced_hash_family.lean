-- Prove2me | solution 1 for mme_CW_2376_exact_profile_induced_hash_family
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T20:22:28.816596+00:00
-- url     : https://prove2.me/submissions/47895633-4283-4c9b-9e4b-227b73437fc0

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Factorial.NatCast
import Definitions.Def_mme_CW_2376_profile_induced_family
import Theorems.Thm_mme_CW_2376_full_marginal_hash_target_collision_budget
import Theorems.Thm_mme_CW_2376_vertex_closed_target_pruning_assembles

open MME Filter

theorem solution :
    ∀ᶠ m : ℕ in atTop,
      let N := cw2376ProfileLength m
      let V : ℝ :=
        (N.factorial : ℝ) /
          (((384072 * m).factorial : ℝ) *
            ((1308290 * m).factorial : ℝ) *
            ((1231903 * m).factorial : ℝ) *
            ((75036 * m).factorial : ℝ) *
            ((699 * m).factorial : ℝ))
      ∃ F : Finset (CW2376ExactProfileAddress m),
        CW2376InducedModeDisjoint F ∧
        V * Real.exp
          (-100000 * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
            (F.card : ℝ) := by
  have hbudget := mme_CW_2376_full_marginal_hash_target_collision_budget
  filter_upwards [hbudget] with m hm
  dsimp only at hm ⊢
  obtain ⟨E, hclosed, hbudgetE⟩ := hm
  obtain ⟨F, hF, hprune⟩ :=
    mme_CW_2376_vertex_closed_target_pruning_assembles m E hclosed
  refine ⟨F, hF, ?_⟩
  linarith
