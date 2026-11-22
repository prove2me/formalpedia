-- Prove2me | solution 1 for polychromNumber_three_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:48:54.17643+00:00
-- url     : https://prove2.me/submissions/dd2f27d2-18cd-4eff-a9db-7507d4331002

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Theorems.Thm_polychromNumber_subset
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_polychromNumber_univ
import Theorems.Thm_polychromNumber_pair
import Theorems.Thm_polychromNumber_le_of_forall
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ


attribute [local simp] polychromNumber_singleton
attribute [local simp] polychromNumber_univ
attribute [local simp] polychromNumber_pair

set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise
theorem _root_.solution : polychromNumber (G := ℤ) {0, 1, 3} = 2 := by
-- ANCHOR_END: polychromNumber_three_eq_two
  set S : Finset ℤ := {0, 1, 3}
  refine le_antisymm ?hard ?easy
  case easy =>
    exact (polychromNumber_subset (S' := {0, 1}) (by simp [S])).trans' (by simp)
  case hard =>
    apply polychromNumber_le_of_forall
    intro χ hχ
    have h1 : ∃ i ∈ S, χ i = χ 2 := by simpa using hχ 0 (χ 2)
    have h2 : ∀ i ∈ S, ∃ n ∈ ({-1, 1, 2} : Finset ℤ), i ∈ n +ᵥ S ∧ 2 ∈ n +ᵥ S := by decide
    obtain ⟨n, hn⟩ : ∃ n : ℤ, ¬ Set.InjOn χ (n +ᵥ S) := by
      obtain ⟨i, hi, hi2⟩ := h1
      obtain ⟨n, hn, hin, h2n⟩ := h2 i (by simpa)
      use n
      simp only [Set.InjOn, not_forall, exists_prop]
      exact ⟨i, hin, 2, h2n, hi2, by clear hin hi2; revert i; decide⟩
    simp_rw [isPolychrom_iff_surjOn, ← Finset.coe_univ] at hχ
    apply hn
    exact Finset.injOn_of_surjOn_of_card_le _ (by simp [Set.mapsTo_univ]) (hχ n) (by simp [S])
