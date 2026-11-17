-- Prove2me | solution 1 for ex_2_1_2_reals_uncountable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:21:43.334477+00:00
-- url     : https://prove2.me/submissions/af45102c-b49b-423e-8138-74ea97b68a62

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_1_F000
import Definitions.Def_ProbabilityTheory_chapter_02_ex_2_1_2_F000
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Tactic
import Theorems.Thm_ex_2_1_2_binary_sequences_no_nat_injection


/-

  Example 2.1.2 Cantor's diagonal argument

-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped Set
open scoped BigOperators

noncomputable section


theorem solution :
    ¬ IsCountableSet (Set.univ : Set ℝ) := by
  rintro ⟨e⟩
  exact ex_2_1_2_binary_sequences_no_nat_injection ⟨
    fun s => (e ⟨cantorIntervalValue s, by trivial⟩).1,
    by
      intro s t hst
      have heq :
          e ⟨cantorIntervalValue s, by trivial⟩ =
            e ⟨cantorIntervalValue t, by trivial⟩ := by
        ext
        exact hst
      have hsub :
          (⟨cantorIntervalValue s, by trivial⟩ : (Set.univ : Set ℝ)) =
            ⟨cantorIntervalValue t, by trivial⟩ := e.injective heq
      have hval := congrArg Subtype.val hsub
      apply cantorIntervalEmbedding_injective
      exact Subtype.ext hval⟩