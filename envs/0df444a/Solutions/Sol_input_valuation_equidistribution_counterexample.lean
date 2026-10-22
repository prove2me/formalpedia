-- Prove2me | solution 1 for input_valuation_equidistribution_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:10:37.951701+00:00
-- url     : https://prove2.me/submissions/4e87319e-dfb4-4541-ab27-07a7481870a9

import Mathlib
import Definitions.Def_syracuseOrbitMin
set_option autoImplicit false

noncomputable section

attribute [instance] Classical.propDecidable

theorem solution :
    ∃ (n₀ m : ℕ) (ā : Fin n₀ → ℕ),
      1 ≤ n₀ ∧ (∀ j, 1 ≤ ā j) ∧ Finset.sum Finset.univ (fun j => ā j) ≤ m ∧
        (Finset.filter (fun r => Odd r ∧ (fun j : Fin n₀ => Nat.factorization (3 * (syracuseStep^[j.val] r) + 1) 2) = ā) (Finset.range (2 ^ m))).card
          ≠ 2 ^ (m - Finset.sum Finset.univ (fun j => ā j)) := by
  refine ⟨1, 1, fun _ => 1, le_rfl, fun _ => le_rfl, by simp, ?_⟩
  have hf : Nat.factorization 4 2 = 2 := by
    have : (4:ℕ) = 2 ^ 2 := by norm_num
    rw [this, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  have hempty : (Finset.filter (fun r => Odd r ∧ (fun j : Fin 1 => Nat.factorization (3 * (syracuseStep^[j.val] r) + 1) 2) = (fun _ => 1)) (Finset.range (2 ^ 1))) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro r hr
    have hr' : r < 2 := by simpa using hr
    rintro ⟨hodd, heq⟩
    interval_cases r
    · exact absurd hodd (by decide)
    · have := congrFun heq 0
      simp at this
      norm_num at this
      rw [hf] at this
      omega
  rw [hempty]
  simp
