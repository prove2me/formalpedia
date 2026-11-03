-- Prove2me | solution 1 for int_matrix_unipotent
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:27:31.479203+00:00
-- url     : https://prove2.me/submissions/b486557c-172b-4838-9d34-c6a53071c090

import Mathlib
import Definitions.Def_OAIQ093D001

section
-- module Solutions.OAIQ093_PR.MatrixSubsum
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Eigenvalues of integer matrices and unipotence

That an integer matrix whose orbit grows polynomially has all eigenvalues of norm `1`, and is
therefore unipotent after passing to a power.

Root of the `Gromov.MatrixSubsum` hierarchy.
-/


open scoped Finset
open scoped Pointwise


theorem LinearMap.toMatrix'_pow {R : Type*} [CommSemiring R] {m : Type*} [Fintype m] [DecidableEq m] (f : (m → R) →ₗ[R] m → R) (n: ℕ):
    LinearMap.toMatrix' (f^n) = (LinearMap.toMatrix' f)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    rw [LinearMap.toMatrix'_mul]
    rw [pow_succ]
    rw [ih]

lemma int_matrix_unipotent_oai {d: ℕ} (hd: 0 < d) (n: ℕ) (hn: 0 < n) (A: (Matrix (Fin d) (Fin d) ℤ)ˣ) (eigen_one_complex: ∀ k : Module.End.Eigenvalues ((A.val.map (Int.castRingHom ℂ ))).toLin', ‖k.val‖ = 1): ∃ m, (A.val^(n * KroneckerPow A eigen_one_complex) - 1)^m = 0 := by
  classical
  let A_C := (A.val.map (Int.castRingHom ℂ ))

  have char_nonzero: A_C.charpoly ≠ 0 := by
    by_contra!
    have monic := A_C.charpoly_monic
    simp [this] at monic

  have eigen_nonzero: ∀ (k : Module.End.Eigenvalues A_C.toLin'), k.val ≠ 0 := by
    intro k
    by_contra!
    have eigen_zero := LinearMap.hasEigenvalue_zero_tfae (A_C.toLin')
    have det_zero := (eigen_zero.out 0 3).mp
    have has_k := k.prop
    conv at has_k =>
      lhs
      equals k.val => rfl

    simp [this] at has_k
    specialize det_zero has_k
    have a_det := Matrix.GeneralLinearGroup.det_ne_zero A
    unfold A_C at det_zero
    simp at det_zero
    conv at det_zero =>
      lhs
      arg 1
      equals (A.val).map (Int.castRingHom ℂ) =>
        simp
    rw [← RingHom.mapMatrix_apply] at det_zero
    simp at det_zero
    apply_fun (fun a => (Int.castRingHom ℂ) a) at a_det
    . conv at a_det =>
        rhs
        simp
      rw [RingHom.map_det] at a_det
      simp at a_det
      contradiction
    . simp
      exact Int.cast_injective

  have eigen_root_unity: ∀ (k : Module.End.Eigenvalues A_C.toLin'), ∃ n, 0 < n ∧ k.val^n = 1 := by
    intro k
    have k_prop := k.property
    conv at k_prop =>
      equals Module.End.HasEigenvalue A_C.toLin' (↑k) =>
        rfl
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly] at k_prop


    have k_mem_roots: ↑k.val ∈ A_C.toLin'.charpoly.rootSet ℂ := by
      simp at k_prop
      simp [Polynomial.mem_rootSet]
      refine ⟨char_nonzero, ?_⟩
      exact k_prop

    have foo := Polynomial.pow_eq_one_of_mahlerMeasure_eq_one ?_ ?_ ?_ (z := (k.val : ℂ)) (p := A.val.charpoly)
    . obtain ⟨n, hn, z_pow⟩ := foo
      use n
    .
      rw [Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
      rw [Polynomial.Monic.leadingCoeff]
      .
        simp
        apply Multiset.prod_eq_one
        intro x hx
        simp at hx
        obtain ⟨a, ⟨charpoly_nonzero, a_root⟩, x_eq⟩ := hx
        rw [← x_eq]
        simp
        apply le_of_eq
        apply eigen_one_complex ⟨a, ?_⟩
        conv =>
          equals Module.End.HasEigenvalue A_C.toLin' a => rfl
        rw [Module.End.hasEigenvalue_iff_isRoot_charpoly]
        simp
        simp [A_C]
        rw [← Matrix.charpoly_map] at a_root
        simpa using a_root

      . apply Polynomial.Monic.map
        apply Matrix.charpoly_monic

    . apply eigen_nonzero
    . simp
      simp [A_C] at char_nonzero
      refine ⟨?_, ?_⟩
      .
        rw [← Matrix.charpoly_map]
        exact char_nonzero
      .
        rw [← Matrix.charpoly_map]
        rw [Polynomial.mem_rootSet] at k_mem_roots
        have foo := k_mem_roots.2
        simp at foo
        simp [A_C] at foo
        exact foo


  let eigen_pow (k: ℂ) (hk: Module.End.HasEigenvalue A_C.toLin' k) := (eigen_root_unity ⟨k, hk⟩).choose
  have eigen_pow_self (k: ℂ) (hk: Module.End.HasEigenvalue A_C.toLin' k): k^(eigen_pow k hk) = 1 := by
    have spec := (eigen_root_unity ⟨k, hk⟩).choose_spec
    obtain ⟨_, pow_eq⟩ := spec
    rw [← pow_eq]
    rfl

  let n_prod := KroneckerPow A eigen_one_complex
  have n_prod_pos: 0 < n_prod := by
    simp [n_prod, KroneckerPow]
    intro k
    by_contra!
    simp at this

    simp [KroneckerPow_single] at this
    grind

  have eigen_pow_prod_one: ∀ k:  Module.End.Eigenvalues A_C.toLin', k.val^(n*n_prod) = 1 := by
    intro k
    unfold n_prod KroneckerPow
    rw [← Finset.mul_prod_erase (f := fun (a: Module.End.Eigenvalues (Matrix.toLin' ((A.val).map ⇑(Int.castRingHom ℂ)))) => KroneckerPow_single A a eigen_one_complex) (a := k)]
    .
      rw [pow_mul]
      have pow_self := eigen_pow_self (k := k.val) (hk := k.prop)
      simp [KroneckerPow_single]
      simp [eigen_pow] at pow_self
      simp_rw [← pow_mul]
      rw [← mul_assoc]
      rw [mul_comm (a := n)]
      rw [mul_assoc]
      rw [pow_mul]
      rw [pow_self]
      simp
    . apply Finset.mem_univ

  have pow_eigen: ∀ j: Module.End.Eigenvalues (A_C.toLin'^(n*n_prod)), j.val = 1 := by
    intro a
    have a_spec := a.prop
    conv at a_spec =>
      equals Module.End.HasEigenvalue (A_C.toLin' ^ (n*n_prod)) (↑a) => rfl
    rw [Module.End.hasEigenvalue_iff_mem_spectrum] at a_spec
    simp_rw [← Matrix.toLin'_pow] at a_spec
    simp [-Matrix.toLin'_pow] at a_spec
    rw [spectrum.map_pow_of_pos _ (by positivity)] at a_spec
    simp at a_spec
    obtain ⟨k, k_mem, k_pow⟩ := a_spec
    simp [Module.End.UnifEigenvalues.val] at k_pow
    conv at k_pow =>
      rhs
      equals Module.End.Eigenvalues.val _ a => rfl

    rw [← k_pow]
    rw [← Matrix.spectrum_toLin'] at k_mem
    rw [← Module.End.hasEigenvalue_iff_mem_spectrum] at k_mem
    rw [← eigen_pow_prod_one (k := ⟨k, k_mem⟩)]
    . simp

  have char_nonzero: (A_C.toLin' ^ (n*n_prod)).charpoly ≠ 0 := by
    by_contra!
    have foo := (A_C.toLin'^(n*n_prod)).charpoly_monic
    simp [this] at foo


  have a_f_char_eq: (A_C.toLin'^(n*n_prod)).charpoly = (Polynomial.X - (Polynomial.C 1))^d := by
    rw [Polynomial.eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (p := (Polynomial.X - Polynomial.C 1) ^ d) (q :=  (A_C.toLin'^(n*n_prod)).charpoly)]
    .
      rw [Polynomial.Monic.def.mp]
      . simp
      . exact LinearMap.charpoly_monic (A_C.toLin' ^ (n*n_prod))
    . simp
      apply Polynomial.Monic.pow
      apply Polynomial.monic_X_sub_C
    .
      have roots_singleton: (A_C.toLin' ^ (n*n_prod)).charpoly.roots.toFinset = {1} := by
        ext a
        simp only [Multiset.mem_toFinset]
        rw [Polynomial.mem_roots']
        simp [-Polynomial.IsRoot.def, char_nonzero]
        rw [← Module.End.hasEigenvalue_iff_isRoot_charpoly]
        refine ⟨?_, ?_⟩
        . intro ha
          specialize pow_eigen ⟨_, ha⟩
          simpa using pow_eigen
        . intro ha

          have ne_zero: NeZero d := by
            apply NeZero.mk
            grind


          obtain ⟨k, hk⟩ := Module.End.exists_eigenvalue (A_C.toLin')
          have k_pow_prod: k^(n*n_prod) = 1 := by
            rw [← eigen_pow_prod_one (k := ⟨k, hk⟩)]
            simp

          rw [ha, ← k_pow_prod]
          apply Module.End.HasEigenvalue.pow
          exact hk

      rw [← Polynomial.le_rootMultiplicity_iff]

      .
        rw [← Polynomial.count_roots]
        rw [Multiset.toFinset_eq_singleton_iff] at roots_singleton
        rw [roots_singleton.2]
        simp

        rw [← Polynomial.Splits.natDegree_eq_card_roots]
        .
          rw [LinearMap.charpoly_natDegree]
          simp
        .
          apply IsAlgClosed.splits
      . by_contra!
        have monic := (A_C.toLin'^(n*n_prod)).charpoly_monic
        simp [this] at monic
    .
      simp only [Polynomial.natDegree_pow]
      rw [Polynomial.natDegree_X_sub_C]
      simp
      rw [LinearMap.charpoly_natDegree]
      simp


  have eval_zero := (A_C.toLin'^(n*n_prod)).aeval_self_charpoly
  simp [a_f_char_eq] at eval_zero
  use d
  simp [A_C] at eval_zero
  apply_fun (fun f => f.toMatrix') at eval_zero
  simp [-EmbeddingLike.map_eq_zero_iff] at eval_zero
  rw [← Matrix.toLin'_pow] at eval_zero
  rw [LinearMap.toMatrix'_pow] at eval_zero
  rw [sub_eq_add_neg, LinearEquiv.map_add] at eval_zero
  rw [LinearMap.toMatrix'_toLin'] at eval_zero
  simp at eval_zero
  apply_fun (fun m => m.map (Int.castRingHom ℂ))
  . simp [-Int.coe_castRingHom]
    rw [Matrix.map_pow]
    rw [Matrix.map_sub]
    .
      rw [sub_eq_add_neg]
      rw [Matrix.map_pow]
      simp
      exact eval_zero
    . simp
  . intro a b hab
    simp at hab
    apply Matrix.map_injective at hab
    .
      exact hab
    . exact Int.cast_injective


open scoped Pointwise Finset
end

theorem solution : type_of% @int_matrix_unipotent_oai := @int_matrix_unipotent_oai
