-- Prove2me | solution 1 for prod_remaining_m_dvd_FRI_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:28:46.591008+00:00
-- url     : https://prove2.me/submissions/a88ad428-3059-4735-a1fb-433ee24b9482

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
import Theorems.Thm_FRI_degree_succ_eq


set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (i : ℕ) (hi : i ≤ P.num_foldings) :
    (∏ j : Fin P.num_foldings with i ≤ j.val, P.m j) ∣ FRI_degree P i := by
  induction i with
  | zero =>
    simp only [Nat.zero_le, Finset.filter_true_of_mem, Finset.mem_univ, implies_true]
    exact P.h_m_dvd_d
  | succ i ih =>
    by_cases hi' : i < P.num_foldings
    · have := ih hi'.le
      rw [FRI_degree_succ_eq P i hi']
      refine Nat.dvd_div_of_mul_dvd ?_
      have h_mem : ⟨i, hi'⟩ ∈ Finset.filter (fun j : Fin P.num_foldings ↦ i ≤ (j : ℕ))
          Finset.univ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩
      rw [← Finset.mul_prod_erase _ _ h_mem, ← Finset.sdiff_singleton_eq_erase] at this
      convert this using 2
      refine Finset.prod_bij (fun j _ ↦ j) ?_ ?_ ?_ ?_
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
          Finset.mem_singleton]
        exact fun a ha ↦ ⟨Nat.le_of_succ_le ha, ne_of_gt (Nat.lt_of_succ_le ha)⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, imp_self, implies_true]
      · simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton, exists_prop, exists_eq_right, and_imp]
        exact fun j hj₁ hj₂ ↦ Nat.succ_le_of_lt (hj₁.lt_of_ne (Fin.val_injective.ne hj₂).symm)
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, implies_true]
    · grind
