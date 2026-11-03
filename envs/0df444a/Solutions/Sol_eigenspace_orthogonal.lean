-- Prove2me | solution 1 for eigenspace_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:17:28.912204+00:00
-- url     : https://prove2.me/submissions/297bb92b-16cc-4f72-9a7a-5cd6d54a2586

import Mathlib

section
-- module Solutions.OAIQ093_PR.ToMathlib_Analysis_Matrix_StarNormalEigen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


lemma star_normal_toContinuousLinearMap {A: Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]  (f: A →ₗ[ℂ] A):
    IsStarNormal f ↔ IsStarNormal (LinearMap.toContinuousLinearMap f) := by

  rw [isStarNormal_iff]
  rw [isStarNormal_iff]
  rw [ContinuousLinearMap.star_eq_adjoint]
  rw [← LinearMap.adjoint_toContinuousLinearMap]
  rw [LinearMap.star_eq_adjoint]
  rw [commute_iff_eq]
  rw [commute_iff_eq]
  rw [LinearMap.ext_iff]
  rw [ContinuousLinearMap.ext_iff]
  simp

-- https://math.stackexchange.com/a/4217008/367657
lemma eigenvalue_adjoint {A: Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A] {f: Module.End ℂ A} {k: ℂ} {v: A} (hf: IsStarNormal f):
  f.HasEigenvector k v ↔ (star f).HasEigenvector (star k) v := by

  -- TODO - figure out a way to re-use 'spectrum.map_star'
  have hf_cont := hf
  rw [star_normal_toContinuousLinearMap] at hf_cont
  rw [Module.End.hasEigenvector_iff]
  rw [Module.End.hasEigenvector_iff]
  have ker_toContinuousLinearMap : ∀ X : A →ₗ[ℂ] A,
      (LinearMap.toContinuousLinearMap X).ker = LinearMap.ker X := fun X => by
    simp [LinearMap.coe_toContinuousLinearMap]
  by_cases v_eq_zero: v = 0
  . simp [v_eq_zero]
  .
    simp only [ne_eq, v_eq_zero, not_false_eq_true, and_true]
    rw [Module.End.eigenspace_def]
    rw [← ker_toContinuousLinearMap]
    rw [← ContinuousLinearMap.IsStarNormal.ker_adjoint_eq_ker]
    .
      rw [← LinearMap.adjoint_toContinuousLinearMap]
      rw [ker_toContinuousLinearMap]
      rw [Module.End.eigenspace_def]
      rw [LinearMap.star_eq_adjoint]
      rw [map_sub]
      rw [LinearEquiv.map_smulₛₗ]
      conv =>
        pattern 1
        equals LinearMap.id =>
          rw [LinearMap.ext_iff]
          simp
      rw [LinearMap.adjoint_id]
      simp
    .
      rw [← star_normal_toContinuousLinearMap]
      apply Commute.isStarNormal_sub
      rw [commute_iff_eq]
      simp

lemma eigenvector_orthogonal {A: Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A] (f: Module.End ℂ A) (j k: ℂ) (v w: A)
  (hf: IsStarNormal f) (hjv: f.HasEigenvector j v) (hkw: f.HasEigenvector k w) (hjk: j ≠ k): inner ℂ v w = 0 := by

  have first_eq: inner ℂ v (f w) = k * (inner ℂ v w) := by
    apply Module.End.HasEigenvector.apply_eq_smul at hkw
    rw [hkw]
    simp

  have second_eq: inner ℂ v (f w) = j * (inner ℂ v w) := by
    rw [← LinearMap.adjoint_inner_left]
    rw [eigenvalue_adjoint hf] at hjv
    apply Module.End.HasEigenvector.apply_eq_smul at hjv
    rw [LinearMap.star_eq_adjoint] at hjv
    rw [hjv]
    rw [inner_smul_left]
    simp

  rw [second_eq] at first_eq
  simp [hjk] at first_eq
  exact first_eq

lemma eigenspace_orthogonal_oai  {A: Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A] (f: Module.End ℂ A) (hf: IsStarNormal f) (j k: ℂ) (hjk: j ≠ k):
    f.eigenspace k ⟂ f.eigenspace j := by

  rw [Submodule.isOrtho_iff_inner_eq]
  intro v hv w hw
  by_cases v_eq_zero: v = 0
  . simp [v_eq_zero]

  by_cases w_eq_zero: w = 0
  . simp [w_eq_zero]
  rw [eigenvector_orthogonal f k j]
  . exact hf
  .
    rw [Module.End.hasEigenvector_iff]
    refine ⟨hv, v_eq_zero⟩
  .
    rw [Module.End.hasEigenvector_iff]
    refine ⟨hw, w_eq_zero⟩
  . exact id (Ne.symm hjk)
end

theorem solution.{u_1} : type_of% @eigenspace_orthogonal_oai.{u_1} := @eigenspace_orthogonal_oai.{u_1}
