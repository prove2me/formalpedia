-- Prove2me | solution 1 for singular_value_zero_le_spectral_norm
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T17:56:13.391052+00:00
-- url     : https://prove2.me/submissions/f952e76f-af52-4a42-a4b1-6ebeec9c0a61

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

open MatrixCompletion Module InnerProductSpace LinearMap

theorem solution :
    ∀ {n₁ n₂ : ℕ} (Y : Matrix (Fin n₁) (Fin n₂) ℝ),
      (Matrix.toEuclideanLin Y).singularValues 0 ≤ spectralNorm Y := by
  intro n₁ n₂ Y
  set T := Matrix.toEuclideanLin Y with hT
  set σ₀ := T.singularValues 0 with hσ₀
  have hσ₀_nonneg : 0 ≤ σ₀ := T.singularValues_nonneg 0
  show σ₀ ≤ ‖(LinearMap.toContinuousLinearMap T)‖
  rcases Nat.eq_zero_or_pos n₂ with hn2 | hn2
  · subst hn2
    have : σ₀ = 0 := by
      rw [hσ₀]; exact (Matrix.toEuclideanLin Y).singularValues_of_finrank_le (by simp)
    rw [this]; positivity
  · set S := (LinearMap.adjoint T) ∘ₗ T with hS_def
    have hSsym : S.IsSymmetric := T.isSymmetric_adjoint_comp_self
    have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin n₂)) = n₂ := by simp
    set b := hSsym.eigenvectorBasis hfr with hb
    set v₀ := b ⟨0, hn2⟩ with hv₀
    have hv₀_norm : ‖v₀‖ = 1 := by rw [hv₀]; exact b.orthonormal.1 _
    have hlam : hSsym.eigenvalues hfr ⟨0, hn2⟩ = σ₀^2 := by
      have hsq := T.sq_singularValues_fin hfr ⟨0, hn2⟩
      simpa [hσ₀] using hsq.symm
    have hTv_sq : ‖T v₀‖^2 = σ₀^2 := by
      have h1 : (inner ℝ (S v₀) v₀ : ℝ) = ‖T v₀‖^2 := by
        rw [hS_def]; simp only [LinearMap.comp_apply]
        rw [LinearMap.adjoint_inner_left T v₀ (T v₀), real_inner_self_eq_norm_sq]
      have h2 : S v₀ = (hSsym.eigenvalues hfr ⟨0, hn2⟩ : ℝ) • v₀ := by
        rw [hv₀, hb]; exact hSsym.apply_eigenvectorBasis hfr ⟨0, hn2⟩
      rw [h2] at h1
      rw [inner_smul_left] at h1
      simp only [conj_trivial, real_inner_self_eq_norm_sq, hv₀_norm] at h1
      rw [hlam] at h1; simp at h1; linarith [h1]
    have hTv : ‖T v₀‖ = σ₀ := by
      have hnn : 0 ≤ ‖T v₀‖ := norm_nonneg _
      nlinarith [sq_nonneg (‖T v₀‖ - σ₀), sq_nonneg (‖T v₀‖ + σ₀)]
    have hbound : ‖T v₀‖ ≤ ‖(LinearMap.toContinuousLinearMap T)‖ * ‖v₀‖ := by
      have := (LinearMap.toContinuousLinearMap T).le_opNorm v₀; simpa using this
    rw [hTv, hv₀_norm, mul_one] at hbound; exact hbound
