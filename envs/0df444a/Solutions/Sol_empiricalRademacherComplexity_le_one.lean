-- Prove2me | solution 1 for empiricalRademacherComplexity_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:39:27.740048+00:00
-- url     : https://prove2.me/submissions/819ccd0d-546d-4e95-ae1d-83f1883c34b8

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Theorems.Thm_rademacherCorrelation_abs_le_one

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u)
    (C : ConceptClass X Bool) {m : ℕ} (hm : 0 < m) (xs : Fin m → X) :
    EmpiricalRademacherComplexity X C xs ≤ 1 := by
  unfold EmpiricalRademacherComplexity
  rw [dif_neg (by omega)]
  have hnum_pos : (0 : ℝ) < (Fintype.card (SignVector m) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have h_each_le_one : ∀ σ : SignVector m,
      sSup { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } ≤ 1 := by
    intro σ
    by_cases hC : C.Nonempty
    · apply csSup_le
      · obtain ⟨h, hh⟩ := hC
        exact ⟨rademacherCorrelation h σ xs, h, hh, rfl⟩
      · rintro r ⟨h, _, rfl⟩
        exact le_trans (le_abs_self _) (rademacherCorrelation_abs_le_one hm h σ xs)
    · rw [Set.not_nonempty_iff_eq_empty] at hC
      simp_all
  have h_sum_le : ∑ σ : SignVector m,
      sSup { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } ≤
      Fintype.card (SignVector m) := by
    calc ∑ σ : SignVector m, sSup _ ≤ ∑ _σ : SignVector m, (1 : ℝ) :=
          Finset.sum_le_sum (fun σ _ => h_each_le_one σ)
      _ = Fintype.card (SignVector m) := by simp [Finset.sum_const, Finset.card_univ]
  calc 1 / (Fintype.card (SignVector m) : ℝ) *
      ∑ σ, sSup { r | ∃ h ∈ C, r = rademacherCorrelation h σ xs }
      ≤ 1 / (Fintype.card (SignVector m) : ℝ) * Fintype.card (SignVector m) := by
        apply mul_le_mul_of_nonneg_left h_sum_le
        exact div_nonneg one_pos.le hnum_pos.le
    _ = 1 := by field_simp
