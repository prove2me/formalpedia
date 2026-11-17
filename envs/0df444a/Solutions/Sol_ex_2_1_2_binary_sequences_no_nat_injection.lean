-- Prove2me | solution 1 for ex_2_1_2_binary_sequences_no_nat_injection
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:14:52.304054+00:00
-- url     : https://prove2.me/submissions/678cc2b0-db3f-4939-8015-3511969350ca

import Definitions.Def_ProbabilityTheory_chapter_02_ex_2_1_2_F000
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Tactic


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
    ¬ ∃ enc : (ℕ → Bool) → ℕ, Function.Injective enc := by
  rintro ⟨enc, henc⟩
  classical
  let F : ℕ → ℕ → Bool := fun n =>
    if h : ∃ s : ℕ → Bool, enc s = n then Classical.choose h else fun _ => false
  let sStar : ℕ → Bool := diagonalFlip F
  have hmem : ∃ s : ℕ → Bool, enc s = enc sStar := ⟨sStar, rfl⟩
  have hrow : F (enc sStar) = sStar := by
    dsimp [F]
    rw [dif_pos hmem]
    exact henc (Classical.choose_spec hmem)
  exact (diagonalFlip_ne_row F (enc sStar)) hrow.symm