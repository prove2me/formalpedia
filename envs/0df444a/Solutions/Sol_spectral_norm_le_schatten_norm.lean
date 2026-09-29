-- Prove2me | solution 1 for spectral_norm_le_schatten_norm
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T13:54:09.614775+00:00
-- url     : https://prove2.me/submissions/3c7f8ac6-3953-49b9-b9bc-59dedf367658

import Definitions.Def_matrix_completion_schatten
import Theorems.Thm_spectral_norm_le_singular_value_zero
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MatrixCompletion

theorem solution :
    ∀ {n₁ n₂ : ℕ} (q : ℕ) (Y : Matrix (Fin n₁) (Fin n₂) ℝ),
      1 ≤ q →
      spectralNorm Y ≤ schattenNorm (q : ℝ) Y := by
  intro n₁ n₂ q Y hq
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hq
  have hqne : (q:ℝ) ≠ 0 := ne_of_gt hq0
  set T := Matrix.toEuclideanLin Y with hT
  have hsv_nonneg : ∀ k : ℕ, 0 ≤ T.singularValues k := fun k => T.singularValues_nonneg k
  rcases Nat.eq_zero_or_pos n₂ with hn2 | hn2
  · -- n₂ = 0 : domain trivial, both norms vanish
    subst hn2
    have hsch : schattenNorm (q:ℝ) Y = 0 := by
      simp only [schattenNorm, Finset.univ_eq_empty, Finset.sum_empty]
      exact Real.zero_rpow (inv_ne_zero hqne)
    rw [hsch]
    have h1 : spectralNorm Y ≤ T.singularValues 0 := spectral_norm_le_singular_value_zero Y
    have hTzero : T = 0 := by
      apply LinearMap.ext
      intro x
      have hx : x = 0 := Subsingleton.elim _ _
      simp [hx]
    have hsv0 : T.singularValues 0 = 0 := by
      rw [hTzero, LinearMap.singularValues_zero, Finsupp.coe_zero, Pi.zero_apply]
    rw [hsv0] at h1
    exact h1
  · -- n₂ ≥ 1 : 0 is a valid index, σ_0 ≤ (∑ σ_k^q)^{1/q}
    have h1 : spectralNorm Y ≤ T.singularValues 0 := spectral_norm_le_singular_value_zero Y
    have hsv0_nonneg : 0 ≤ T.singularValues 0 := hsv_nonneg 0
    have h2 : T.singularValues 0 = Real.rpow (Real.rpow (T.singularValues 0) (q:ℝ)) (q:ℝ)⁻¹ :=
      (Real.rpow_rpow_inv hsv0_nonneg hqne).symm
    have h3 : Real.rpow (T.singularValues 0) (q:ℝ)
        ≤ ∑ k : Fin n₂, Real.rpow (T.singularValues (k:ℕ)) (q:ℝ) := by
      have hmem : (⟨0, hn2⟩ : Fin n₂) ∈ (Finset.univ : Finset (Fin n₂)) := Finset.mem_univ _
      have := Finset.single_le_sum
        (f := fun k : Fin n₂ => Real.rpow (T.singularValues (k:ℕ)) (q:ℝ))
        (fun k _ => Real.rpow_nonneg (hsv_nonneg _) _) hmem
      simpa using this
    have hinv_nonneg : 0 ≤ (q:ℝ)⁻¹ := by positivity
    have h4 : Real.rpow (Real.rpow (T.singularValues 0) (q:ℝ)) (q:ℝ)⁻¹
        ≤ schattenNorm (q:ℝ) Y := by
      show Real.rpow (Real.rpow (T.singularValues 0) (q:ℝ)) (q:ℝ)⁻¹
        ≤ Real.rpow (∑ k : Fin n₂, Real.rpow (T.singularValues (k:ℕ)) (q:ℝ)) (q:ℝ)⁻¹
      exact Real.rpow_le_rpow (Real.rpow_nonneg hsv0_nonneg _) h3 hinv_nonneg
    calc spectralNorm Y ≤ T.singularValues 0 := h1
      _ = Real.rpow (Real.rpow (T.singularValues 0) (q:ℝ)) (q:ℝ)⁻¹ := h2
      _ ≤ schattenNorm (q:ℝ) Y := h4
