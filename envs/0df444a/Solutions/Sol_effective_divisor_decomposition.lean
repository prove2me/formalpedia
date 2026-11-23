-- Prove2me | solution 1 for effective_divisor_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:44:08.724297+00:00
-- url     : https://prove2.me/submissions/aef8f1f7-dfd7-496c-adaf-a38d336991d7

module
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Definitions.Def_ChipFiringWithLean_Basic
public import Theorems.Thm_deg_one_chip
attribute [local simp] deg_one_chip

set_option autoImplicit true
@[expose] public section
public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty
theorem _root_.solution (G : CFGraph) (E'' : CFDiv G) (k₁ k₂ : ℕ)
  (h_effective : effective E'') (h_deg : deg E'' = k₁ + k₂) :
  ∃ (E₁ E₂ : CFDiv G),
    effective E₁ ∧ effective E₂ ∧
    deg E₁ = k₁ ∧ deg E₂ = k₂ ∧
    E'' = E₁ + E₂ := by

  let can_split (E : CFDiv G) (a b : ℕ): Prop :=
    ∃ (E₁ E₂ : CFDiv G),
      effective E₁ ∧ effective E₂ ∧
      deg E₁ = a ∧ deg E₂ = b ∧
      E = E₁ + E₂

  let P (a b : ℕ) : Prop := ∀ (E : CFDiv G),
    effective E → deg E = a + b → can_split E a b

  have h_ind (a b : ℕ): P a b := by
    induction a with
    | zero =>
    . -- Base case: a = 0
      intro E h_eff h_deg
      use (0 : CFDiv G), E
      constructor
      -- E₁ is effective
      dsimp only [effective, Pi.zero_apply]
      intro v
      linarith
      -- E₂ is effective
      constructor
      exact h_eff
      -- deg E₁ = 0
      constructor
      simp only [_root_.map_zero, CharP.cast_eq_zero]
      -- deg E₂ = b
      constructor
      rw[h_deg]
      simp only [CharP.cast_eq_zero, zero_add]
      -- E = 0 + E
      simp only [zero_add]
    | succ a ha =>
    . -- Inductive step: assume P a b holds, prove P (a+1) b
      dsimp only [Int.natCast_add, Int.cast_ofNat_Int, P] at *
      intro E E_effective E_deg
      have ex_v : ∃ (v : G.V), E v ≥ 1 := by
        by_contra h_contra
        push Not at h_contra
        have h_sum : deg E = 0 := by
          dsimp only [deg, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
          rw [Finset.sum_eq_zero_iff_of_nonneg (fun v _ => E_effective v)]
          intro v hv
          have h_nonneg : 0 ≤ E v := E_effective v
          specialize h_contra v
          linarith
        rw [h_sum] at E_deg
        linarith
      rcases ex_v with ⟨v, hv_ge_one⟩
      let E' := E - one_chip v
      have h_E'_effective : effective E' := by
        intro w
        dsimp only [Pi.sub_apply, E']
        by_cases hw : w = v
        · rw [hw]
          specialize hv_ge_one
          dsimp only [one_chip]
          simp only [↓reduceIte, Int.sub_nonneg]
          linarith
        · specialize E_effective w
          dsimp only [one_chip]
          simp only [hw, ↓reduceIte, sub_zero, ge_iff_le]
          linarith
      specialize ha E' h_E'_effective
      have h_deg_E' : deg E' = a + b := by
        dsimp only [E']; simp only [map_sub, deg_one_chip]; omega
      apply ha at h_deg_E'
      rcases h_deg_E' with ⟨E₁, E₂, h_E1_eff, h_E2_eff, h_deg_E1, h_deg_E2, h_eq_split⟩
      use E₁ + one_chip v, E₂
      -- Check E₁ + one_chip v is effective
      constructor
      apply (Eff G).add_mem
      -- E₁ is effective
      exact h_E1_eff
      -- one_chip v is effective
      intro w
      dsimp only [one_chip]
      simp only [ge_iff_le]
      by_cases hw : w = v
      rw [hw]
      simp only [↓reduceIte, zero_le_one]
      simp only [hw, ↓reduceIte, Std.le_refl]
      -- E₂ is effective
      constructor
      exact h_E2_eff
      -- deg (E₁ + one_chip v) = a + 1
      constructor
      simp only [_root_.map_add, h_deg_E1, deg_one_chip, Nat.cast_add, Nat.cast_one]
      -- deg E₂ = b
      constructor
      exact h_deg_E2
      -- E = (E₁ + one_chip v) + E₂
      dsimp only [E'] at h_eq_split
      rw [add_assoc, add_comm (one_chip v), ← add_assoc, ← h_eq_split]
      abel

  exact h_ind k₁ k₂ E'' h_effective h_deg
