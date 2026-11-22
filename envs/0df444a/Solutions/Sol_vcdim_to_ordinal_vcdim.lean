-- Prove2me | solution 1 for vcdim_to_ordinal_vcdim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:44:31.397147+00:00
-- url     : https://prove2.me/submissions/77b54a52-7e7f-4729-9ea9-109fc4f8a2ca

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Data
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Ordinal
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Bayesian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Bridge
public import Theorems.Thm_ordinalVCDim_inner_bddAbove
public import Theorems.Thm_ordinalVCDim_outer_bddAbove


set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u)
    (C : ConceptClass X Bool) :
    withTopNatToOrdinal (VCDim X C) ≤ OrdinalVCDim X C := by
  have : Nonempty (Finset X) := ⟨∅⟩
  rcases hv : VCDim X C with _ | n
  · -- INFINITE CASE: VCDim X C = ⊤, withTopNatToOrdinal ⊤ = ω
    simp only [withTopNatToOrdinal]
    rw [Ordinal.omega0_le]
    intro m
    obtain ⟨S, hS_lt⟩ := iSup_eq_top.mp (show VCDim X C = ⊤ from hv)
      (↑m) (WithTop.coe_lt_top m)
    have hS_shat : Shatters X C S := by
      by_contra hns
      simp_all
    rw [iSup_pos hS_shat] at hS_lt
    calc (↑m : Ordinal) ≤ ↑S.card :=
          Nat.cast_le.mpr (le_of_lt (by exact_mod_cast hS_lt))
      _ ≤ ⨆ (_ : Shatters X C S), ((S.card : ℕ) : Ordinal) :=
          le_ciSup (ordinalVCDim_inner_bddAbove X C S) hS_shat
      _ ≤ OrdinalVCDim X C :=
          le_ciSup_of_le (ordinalVCDim_outer_bddAbove X C) S le_rfl
  · -- FINITE CASE: VCDim X C = ↑n, withTopNatToOrdinal (↑n) = (n : Ordinal)
    simp only [withTopNatToOrdinal]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact bot_le
    · -- n > 0: extract witness via contradiction (same as VCDim_embed_ordinal)
      have ⟨S₀, hS₀_shat, hS₀_card⟩ : ∃ S₀, Shatters X C S₀ ∧ S₀.card = n := by
        by_contra h_none
        push Not at h_none
        have : ∀ S, Shatters X C S → S.card ≤ n - 1 := by
          intro S hS
          have hle : S.card ≤ n := by
            have : (S.card : WithTop ℕ) ≤ ↑n := by
              calc (S.card : WithTop ℕ)
                  ≤ ⨆ (S : Finset X) (_ : Shatters X C S), (S.card : WithTop ℕ) :=
                    le_iSup₂ (f := fun (S : Finset X) (_ : Shatters X C S) =>
                      (S.card : WithTop ℕ)) S hS
                _ = ↑n := hv
            exact WithTop.coe_le_coe.mp this
          have hne := h_none S hS
          omega
        have hbound : VCDim X C ≤ ↑(n - 1) := by
          apply iSup₂_le
          simp_all
        rw [hv] at hbound
        have : n ≤ n - 1 := WithTop.coe_le_coe.mp hbound
        omega
      calc (↑n : Ordinal) = ↑S₀.card := by exact_mod_cast hS₀_card.symm
        _ ≤ ⨆ (_ : Shatters X C S₀), ((S₀.card : ℕ) : Ordinal) :=
            le_ciSup (ordinalVCDim_inner_bddAbove X C S₀) hS₀_shat
        _ ≤ OrdinalVCDim X C :=
            le_ciSup_of_le (ordinalVCDim_outer_bddAbove X C) S₀ le_rfl
