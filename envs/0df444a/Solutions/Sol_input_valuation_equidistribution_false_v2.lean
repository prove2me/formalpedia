-- Prove2me | solution 1 for input_valuation_equidistribution_false_v2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:10:05.424341+00:00
-- url     : https://prove2.me/submissions/87b598a5-429b-47a5-b7d0-96e2c2e37ed3

import Mathlib
import Definitions.Def_syracuseOrbitMin
set_option autoImplicit false

noncomputable section

attribute [instance] Classical.propDecidable

theorem solution :
    ¬ ∀ n₀ m : ℕ, 1 ≤ n₀ → ∀ ā : Fin n₀ → ℕ, (∀ j, 1 ≤ ā j) →
      Finset.sum Finset.univ (fun j => ā j) ≤ m →
      (Finset.filter (fun r => Odd r ∧ (fun j : Fin n₀ => Nat.factorization (3 * (syracuseStep^[j.val] r) + 1) 2) = ā) (Finset.range (2 ^ m))).card
        = 2 ^ (m - Finset.sum Finset.univ (fun j => ā j)) := by
  intro h
  have h1 := h 1 1 le_rfl (fun _ => 1) (fun _ => le_rfl) (by simp)
  have hf : Nat.factorization 4 2 = 2 := by
    have : (4:ℕ) = 2 ^ 2 := by norm_num
    rw [this, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  have hs : syracuseStep^[0] 1 = 1 := rfl
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
  rw [hempty] at h1
  simp at h1
