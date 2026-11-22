-- Prove2me | solution 1 for rademacherComplexity_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:40:06.957043+00:00
-- url     : https://prove2.me/submissions/3b6b83c7-d2c0-4554-b86c-f4f9c8e40067

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Theorems.Thm_rademacherCorrelation_abs_le_one
public import Theorems.Thm_empiricalRademacherComplexity_le_one
section
@[expose] public section
universe u v
private theorem flipAt_involutive {m : ℕ} (i : Fin m) : Function.Involutive (flipAt i) := by
  intro σ; ext k; unfold flipAt
  simp_all
private theorem flipAt_boolToSign {m : ℕ} (i : Fin m) (σ : SignVector m) :
    boolToSign (flipAt i σ i) = -boolToSign (σ i) := by
  unfold flipAt; simp only [Function.update_self]
  unfold boolToSign; cases σ i <;> simp
private theorem flipAt_other {m : ℕ} (i : Fin m) (σ : SignVector m) (k : Fin m) (hk : k ≠ i) :
    flipAt i σ k = σ k := by
  unfold flipAt; simp [hk]
private theorem sum_boolToSign_cancel {m : ℕ} (i : Fin m) (f : SignVector m → ℝ)
    (hf : ∀ σ σ', (∀ k, k ≠ i → σ k = σ' k) → f σ = f σ') :
    ∑ σ : SignVector m, boolToSign (σ i) * f σ = 0 := by
  -- Use the involution flipAt i to show S = -S, hence S = 0.
  have hinv := flipAt_involutive i
  set g : SignVector m → ℝ := fun σ => boolToSign (σ i) * f σ
  -- Reindex: Σ g(σ) = Σ g(flipAt i σ) since flipAt i is a bijection.
  have h_eq : ∑ σ : SignVector m, g σ =
      ∑ σ : SignVector m, g (flipAt i σ) := by
    let e : SignVector m ≃ SignVector m := Equiv.ofBijective (flipAt i) hinv.bijective
    rw [show ∑ σ, g (flipAt i σ) = ∑ σ, g (e σ) from rfl]
    exact (Equiv.sum_comp e g).symm
  -- g(flipAt i σ) = -g(σ) since flipAt negates boolToSign at i but preserves f.
  have h_neg : ∀ σ, g (flipAt i σ) = -g σ := by
    intro σ
    change boolToSign (flipAt i σ i) * f (flipAt i σ) =
      -(boolToSign (σ i) * f σ)
    rw [flipAt_boolToSign, hf (flipAt i σ) σ (fun k hk => flipAt_other i σ k hk)]
    ring
  -- So S = Σ g(σ) = Σ -g(σ) = -S.
  have h_neg_sum : ∑ σ : SignVector m, g σ = -(∑ σ : SignVector m, g σ) := by
    conv_lhs => rw [h_eq]
    simp_rw [h_neg]
    simp [Finset.sum_neg_distrib]
  linarith
private theorem empRad_nonneg {X : Type u} (C : ConceptClass X Bool) {m : ℕ}
    (hm : m ≠ 0) (xs : Fin m → X) :
    0 ≤ EmpiricalRademacherComplexity X C xs := by
  unfold EmpiricalRademacherComplexity
  rw [dif_neg hm]
  apply mul_nonneg
  · apply div_nonneg one_pos.le; exact Nat.cast_nonneg _
  · by_cases hC : C.Nonempty
    · obtain ⟨h₀, hh₀⟩ := hC
      have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
      have hbdd : ∀ σ, BddAbove { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } := by
        intro σ; refine ⟨1, fun r hr => ?_⟩
        obtain ⟨h', _, rfl⟩ := hr
        exact le_trans (le_abs_self _) (rademacherCorrelation_abs_le_one hm_pos h' σ xs)
      have h_ge : ∀ σ : SignVector m,
          rademacherCorrelation h₀ σ xs ≤
            sSup { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } :=
        fun σ => le_csSup_of_le (hbdd σ) ⟨h₀, hh₀, rfl⟩ le_rfl
      have h_sum_corr : ∑ σ : SignVector m, rademacherCorrelation h₀ σ xs = 0 := by
        simp only [rademacherCorrelation, dif_neg hm]
        rw [← Finset.mul_sum, Finset.sum_comm]
        have : ∀ i : Fin m, ∑ σ : SignVector m,
            boolToSign (σ i) * boolToSign (h₀ (xs i)) = 0 :=
          fun i => sum_boolToSign_cancel i (fun _ => boolToSign (h₀ (xs i)))
            (fun _ _ _ => rfl)
        simp [this]
      calc (0 : ℝ) = ∑ σ : SignVector m, rademacherCorrelation h₀ σ xs := h_sum_corr.symm
        _ ≤ ∑ σ : SignVector m,
              sSup { r : ℝ | ∃ h ∈ C, r = rademacherCorrelation h σ xs } :=
            Finset.sum_le_sum (fun σ _ => h_ge σ)
    · rw [Set.not_nonempty_iff_eq_empty] at hC
      simp_all
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (D : MeasureTheory.Measure X) (m : ℕ) (hm : 0 < m)
    [MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.pi (fun _ : Fin m => D))] :
    RademacherComplexity X C D m ≤ 1 := by
  unfold RademacherComplexity
  calc ∫ xs, EmpiricalRademacherComplexity X C xs ∂(MeasureTheory.Measure.pi _)
      ≤ ∫ _xs, (1 : ℝ) ∂(MeasureTheory.Measure.pi (fun _ : Fin m => D)) := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact MeasureTheory.ae_of_all _ (fun xs =>
            empRad_nonneg C (Nat.pos_iff_ne_zero.mp hm) xs)
        · exact MeasureTheory.integrable_const 1
        · exact MeasureTheory.ae_of_all _
            (fun xs => empiricalRademacherComplexity_le_one X C hm xs)
    _ = 1 := by simp [MeasureTheory.integral_const]
