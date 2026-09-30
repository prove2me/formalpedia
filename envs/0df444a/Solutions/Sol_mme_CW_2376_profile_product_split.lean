-- Prove2me | solution 1 for mme_CW_2376_profile_product_split
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:36:55.746131+00:00
-- url     : https://prove2.me/submissions/5dc49a68-5f08-48d3-a1fe-dc3e36550ced

import Mathlib
import Definitions.Def_mme_CW_2376_address_block

open MME BigOperators
set_option autoImplicit false

theorem solution
    {M : Type} [CommMonoid M]
    (Q : (Fin 3 → Fin 5) → M) (m : ℕ) :
    (∏ σ, Q σ ^ cw2376ProfileMultiplicity m σ) =
      (∏ σ ∈ cw2376ScalarTypes, Q σ) ^ (699 * m) *
      (∏ σ ∈ cw2376RectTypes, Q σ) ^ (37518 * m) *
      (∏ σ ∈ cw2376CentralTypes, Q σ) ^ (307638 * m) *
      (∏ σ ∈ cw2376CoupledTypes, Q σ) ^ (616627 * m) := by
  have hdisj : ∀ σ : Fin 3 → Fin 5,
      ¬ (σ ∈ cw2376ScalarTypes ∧ σ ∈ cw2376RectTypes) ∧
      ¬ (σ ∈ cw2376ScalarTypes ∧ σ ∈ cw2376CentralTypes) ∧
      ¬ (σ ∈ cw2376ScalarTypes ∧ σ ∈ cw2376CoupledTypes) ∧
      ¬ (σ ∈ cw2376RectTypes ∧ σ ∈ cw2376CentralTypes) ∧
      ¬ (σ ∈ cw2376RectTypes ∧ σ ∈ cw2376CoupledTypes) ∧
      ¬ (σ ∈ cw2376CentralTypes ∧ σ ∈ cw2376CoupledTypes) := by
    have hSR : Disjoint cw2376ScalarTypes cw2376RectTypes := by decide
    have hSC : Disjoint cw2376ScalarTypes cw2376CentralTypes := by decide
    have hSD : Disjoint cw2376ScalarTypes cw2376CoupledTypes := by decide
    have hRC : Disjoint cw2376RectTypes cw2376CentralTypes := by decide
    have hRD : Disjoint cw2376RectTypes cw2376CoupledTypes := by decide
    have hCD : Disjoint cw2376CentralTypes cw2376CoupledTypes := by decide
    intro σ
    exact ⟨fun h ↦ Finset.disjoint_left.mp hSR h.1 h.2,
      fun h ↦ Finset.disjoint_left.mp hSC h.1 h.2,
      fun h ↦ Finset.disjoint_left.mp hSD h.1 h.2,
      fun h ↦ Finset.disjoint_left.mp hRC h.1 h.2,
      fun h ↦ Finset.disjoint_left.mp hRD h.1 h.2,
      fun h ↦ Finset.disjoint_left.mp hCD h.1 h.2⟩
  calc
    (∏ σ, Q σ ^ cw2376ProfileMultiplicity m σ) =
        ∏ σ, (if σ ∈ cw2376ScalarTypes then Q σ ^ (699 * m) else 1) *
          (if σ ∈ cw2376RectTypes then Q σ ^ (37518 * m) else 1) *
          (if σ ∈ cw2376CentralTypes then Q σ ^ (307638 * m) else 1) *
          (if σ ∈ cw2376CoupledTypes then Q σ ^ (616627 * m) else 1) := by
      apply Finset.prod_congr rfl
      intro σ _
      have h := hdisj σ
      unfold cw2376ProfileMultiplicity
      split_ifs <;> simp_all
    _ = _ := by
      simp only [Finset.prod_mul_distrib, Finset.prod_ite_mem_eq, Finset.prod_pow]
