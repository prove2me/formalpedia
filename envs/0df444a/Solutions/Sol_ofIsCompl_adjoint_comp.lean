-- Prove2me | solution 1 for ofIsCompl_adjoint_comp
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:20:28.897636+00:00
-- url     : https://prove2.me/submissions/f627813e-813e-4ab7-b9ea-fe9d7e933893

import Mathlib

section
-- module Solutions.OAIQ093_PR.ToMathlib_Analysis_Matrix_UnitaryAux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Unitary matrices: helper lemmas

General-purpose material extracted from the Gromov development, destined for mathlib.
-/


lemma ofIsCompl_adjoint_comp_oai {P: Type*} [NormedAddCommGroup P] [CompleteSpace P] [InnerProductSpace ℂ P] [FiniteDimensional ℂ P]  {p q : Submodule ℂ P} (h : IsCompl p q) (hpq: p ⟂ q) (φ : p →ₗ[ℂ] P) (ψ : q →ₗ[ℂ] P) (hφ: (LinearMap.adjoint φ) ∘ₗ φ = 1) (hφ_map: ∀ x: p, φ x ∈ p) (hψ: (LinearMap.adjoint ψ) ∘ₗ ψ = 1) (hψ_map: ∀ x: q, ψ x ∈ q):
  (LinearMap.ofIsCompl h (φ) (ψ)).adjoint ∘ₗ(LinearMap.ofIsCompl h φ ψ) = 1  := by
    rw [LinearMap.ext_iff]
    intro a
    obtain ⟨x, y, a_eq, other⟩ := Submodule.existsUnique_add_of_isCompl h a
    rw [← a_eq]
    simp
    rw [LinearMap.ofIsCompl_eq_add]
    simp

    have adjoint_compl_p_eq : LinearMap.adjoint (p.projectionOnto q h) = p.subtype := by
      rw [eq_comm]
      simp [-Submodule.coe_projectionOnto_apply, LinearMap.eq_adjoint_iff]
      intro b hb z
      obtain ⟨x, y, z_eq, other⟩ := Submodule.existsUnique_add_of_isCompl h z
      rw [← z_eq]
      simp
      rw [inner_add_right]
      simp
      have b_eq : b = (⟨b, hb⟩: p) := by simp
      rw [b_eq]
      apply Submodule.IsOrtho.inner_eq hpq (by simp [hb]) (by simp)

    have adjoint_compl_q_eq : LinearMap.adjoint (q.projectionOnto p h.symm) = q.subtype := by
      rw [eq_comm]
      simp [-Submodule.coe_projectionOnto_apply, LinearMap.eq_adjoint_iff]
      intro b hb z
      obtain ⟨x, y, z_eq, other⟩ := Submodule.existsUnique_add_of_isCompl h z
      rw [← z_eq]
      simp
      rw [inner_add_right]
      simp
      have b_eq : b = (⟨b, hb⟩: q) := by simp
      rw [b_eq]
      apply Submodule.IsOrtho.inner_eq hpq.symm (by simp [hb]) (by simp)

    let temp := φ.adjoint

    have adjoint_phi_eq: (LinearMap.adjoint φ) =  (LinearMap.ofIsCompl h (LinearMap.domRestrict φ.adjoint p) 0) := by
      rw [eq_comm]
      rw [LinearMap.eq_adjoint_iff]
      intro c d
      simp
      obtain ⟨x, y, c_eq, _⟩ := Submodule.existsUnique_add_of_isCompl h c
      rw [← c_eq]
      simp
      rw [inner_add_left]

      rw [Submodule.isOrtho_iff_inner_eq] at hpq
      have my_inner := hpq (φ d) (by exact hφ_map d) y (by simp)
      rw [inner_eq_zero_symm] at my_inner
      simp [my_inner]
      nth_rw 2 [← inner_conj_symm]
      rw [← LinearMap.adjoint_inner_right]
      simp

    have adjoint_psi_eq: (LinearMap.adjoint ψ) =  (LinearMap.ofIsCompl h 0 (LinearMap.domRestrict ψ.adjoint q)) := by
      rw [eq_comm]
      rw [LinearMap.eq_adjoint_iff]
      intro c d
      simp
      obtain ⟨x, y, c_eq, _⟩ := Submodule.existsUnique_add_of_isCompl h c
      rw [← c_eq]
      simp
      rw [inner_add_left]

      rw [Submodule.isOrtho_iff_inner_eq] at hpq
      have my_inner := hpq x (by simp) (ψ d) (by exact hψ_map d)
      simp [my_inner]
      nth_rw 2 [← inner_conj_symm]
      rw [← LinearMap.adjoint_inner_right]
      simp

    simp [adjoint_compl_p_eq, adjoint_compl_q_eq]
    apply_fun (fun f => f x) at hφ
    simp at hφ
    simp [hφ]

    apply_fun (fun f => f y) at hψ
    simp at hψ
    simp [hψ]
    rw [adjoint_phi_eq]
    conv =>
      pattern ψ y
      equals (⟨ψ y, by apply hψ_map⟩ : q).val =>
        simp

    rw [LinearMap.ofIsCompl_apply_right]
    simp

    rw [adjoint_psi_eq]
    conv =>
      lhs
      rhs
      equals (⟨φ x, by apply hφ_map⟩ : p).val =>
        simp


    rw [LinearMap.ofIsCompl_apply_left]
    simp
end

theorem solution.{u_1} : type_of% @ofIsCompl_adjoint_comp_oai.{u_1} := @ofIsCompl_adjoint_comp_oai.{u_1}
