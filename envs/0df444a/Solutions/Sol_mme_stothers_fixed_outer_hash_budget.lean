-- Prove2me | solution 1 for mme_stothers_fixed_outer_hash_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:41:37.520535+00:00
-- url     : https://prove2.me/submissions/a20d44a2-ec1b-43fe-82df-897616c7294c

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Factorial.NatCast
import Definitions.Def_mme_stothers_fixed_outer_profile
import Theorems.Thm_mme_stothers_fixed_target_count_and_completion_degree
import Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_outer_hash_budget_of_degree_data

open BigOperators Filter

set_option autoImplicit false
set_option warningAsError true

theorem solution :
    ∀ᶠ m : ℕ in atTop,
      let N := MME.StothersFourth.fixedOuterLength m
      let V : ℝ :=
        (N.factorial : ℝ) /
          ∏ j : Fin 9,
            ((MME.StothersFourth.fixedMarginalCount m j).factorial : ℝ)
      ∃ E : Finset (MME.StothersFourth.FixedMarginalSupportedAddress m),
        MME.StothersFourth.FixedMarginalVertexClosed E ∧
        ((MME.StothersFourth.fixedTargetAmbientCollisions E).card : ℝ) +
            V * Real.exp
              (-1000000 * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
          ((MME.StothersFourth.fixedExactTargetEdges E).card : ℝ) := by
  exact
    MME.StothersFourth.mme_stothers_fixed_outer_hash_budget_of_degree_data
      mme_stothers_fixed_target_count_and_completion_degree
