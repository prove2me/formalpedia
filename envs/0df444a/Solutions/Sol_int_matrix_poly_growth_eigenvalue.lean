-- Prove2me | solution 1 for int_matrix_poly_growth_eigenvalue
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:25:34.612665+00:00
-- url     : https://prove2.me/submissions/d661ec29-319e-4460-a1ca-c395d1e3caad

import Mathlib
import Definitions.Def_OAIQ093D011

section
-- module Solutions.OAIQ093_PR.MatrixSubsum_Subsums
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Subset sums of matrix powers

The `DerivedSets` machinery and the estimate `subsums_unique`: distinct subsets of `[a,b)` give
distinct sums of `Aᵏ • v` when `A` has an eigenvalue of norm `≥ 3`.
-/


open scoped Finset
open scoped Pointwise

lemma mul_pow_exact {d: ℕ} {R: Type*} [Ring R] (A: Matrix (Fin d) (Fin d) R) (v: (Fin d) → R) (k: R)  (hva: A.vecMul v = (k • v)): ∀ n: ℕ, (A ^ n).vecMul v = ((k ^ n) • v) := by
  intro n
  induction n with
  | zero =>
    simp
  | succ j ih =>
    rw [pow_succ']
    rw [← Matrix.vecMul_vecMul]
    rw [hva]
    rw [Matrix.smul_vecMul]
    rw [ih]
    rw [pow_succ']
    rw [mul_smul]


lemma interval_sum_le {R: Type*} {d: ℕ} [RCLike R] [ NormSMulClass R (Fin d → R)] (A: Matrix (Fin d) (Fin d) R) (φ v: (Fin d) → R) (hv: ‖φ ⬝ᵥ v‖ ≠ 0) (k: R) (hk: 3 ≤ ‖k‖) (hva: A.vecMul φ = k • φ) (a b: ℕ):
    ∑ i ∈ Finset.Ico a b, ‖φ ⬝ᵥ (A ^ i).mulVec v‖ < ‖φ ⬝ᵥ (A ^ b).mulVec v‖ := by


  have mul_pow: ∀ n: ℕ, 3 ^ n * ‖φ ⬝ᵥ v‖ ≤ ‖φ ⬝ᵥ (A ^ n).mulVec v‖ := by
    intro n
    induction n with
    | zero =>
      simp only [pow_zero, one_mul, Matrix.one_mulVec, le_refl]
    | succ j ih =>
      nth_rw 2 [pow_succ']
      rw [← Matrix.mulVec_mulVec]
      rw [Matrix.dotProduct_mulVec]
      rw [hva]
      rw [smul_dotProduct]
      rw [norm_smul]
      rw [pow_succ']
      rw [mul_assoc]
      grw [ih]
      grw [hk]

  by_cases b_le: b ≤ a
  .
    have ico_empty: Finset.Ico a b = ∅ := by
      simpa using b_le


    simp [ico_empty]
    by_contra!
    have norm_le := mul_pow b
    rw [this] at norm_le
    simp at norm_le
    rw [mul_nonpos_iff] at norm_le
    simp at norm_le
    cases norm_le
    . rename_i v_zero
      simp [v_zero] at hv
    . rename_i le_zero
      rw [← Real.rpow_natCast] at le_zero
      have pow_pos := Real.rpow_pos_of_pos (x := 3) (by norm_num) b
      linarith
  .
    simp at b_le
    induction b, b_le using Nat.le_induction with
    | base =>
      simp
      simp_rw [Matrix.dotProduct_mulVec]
      rw [mul_pow_exact A φ k hva]
      rw [mul_pow_exact A φ k hva]
      rw [pow_succ]
      rw [mul_smul]
      simp
      rw [← mul_assoc]
      rw [mul_lt_mul_iff_left₀]
      rw [lt_mul_iff_one_lt_right]
      .
        linarith
      .
        positivity
      . simpa using hv
    | succ n hmn ih =>
      rw [Finset.sum_Ico_succ_top]
      rw [pow_succ']
      rw [← Matrix.mulVec_mulVec]
      nth_rw 2 [Matrix.dotProduct_mulVec]
      rw [hva]
      simp
      rw [Matrix.dotProduct_mulVec]
      rw [mul_pow_exact A φ k hva]
      norm_cast

      rw [Matrix.dotProduct_mulVec] at ih
      rw [mul_pow_exact A φ k hva] at ih
      apply_fun (fun x => x + ‖k‖ ^ n * ‖v‖) at ih
      .
        simp only [] at ih

        norm_cast at ih
        simp at ih
        grw [ih]
        simp
        rw [← two_mul]


        have two_lt_k: (2: ℝ) < ‖k‖:= by
          linarith


        grw [two_lt_k]
      .
        intro a b hab
        simp
        exact hab
      . linarith


theorem hasEigenvalue_of_isRoot_charpoly  {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {f : Module.End R M} {μ : R} [IsDomain R] [Module.Finite R M] [Module.Free R M] (h : (f.charpoly).IsRoot μ) : f.HasEigenvalue μ := by
  simp at h
  rw [LinearMap.eval_charpoly] at h
  have nontrivial_ker := LinearMap.bot_lt_ker_of_det_eq_zero h
  rw [LinearMap.det_eq_zero_iff_ker_ne_bot] at h
  apply Submodule.exists_mem_ne_zero_of_ne_bot at h
  obtain ⟨v, v_mem, v_nonzero⟩ := h
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := v)
  rw [Module.End.hasEigenvector_iff]
  simp
  simp at v_mem
  rw [sub_eq_zero] at v_mem
  rw [eq_comm] at v_mem
  refine ⟨v_mem, v_nonzero⟩

-- TODO - upstream to mathlib
lemma int_matrix_eigenvalue {d: ℕ} (A: (Matrix (Fin d) (Fin d) ℤ)ˣ):
    (∀ (k : ℂ), Module.End.HasEigenvalue ((A.val.map (Int.castRingHom ℂ)).toLin') k → ‖k‖ = 1) ∨ (∃ (k: ℂ), (Module.End.HasEigenvalue ((A.val.map (Int.castRingHom ℂ)).toLin') k) ∧ 1 < ‖k‖) := by

  rw [Classical.or_iff_not_imp_left]
  intro not_all_one
  simp at not_all_one


  obtain ⟨k, hk, hk_not_one⟩ := not_all_one


  .

    --
    have a_det_unit := Matrix.isUnits_det_units A
    rw [Int.isUnit_iff] at a_det_unit
    let A_C := A.val.map (Int.castRingHom ℂ)
    have det_eq := Matrix.det_eq_prod_roots_charpoly A_C
    have foo := Matrix.charpoly_map A.val (Int.castRingHom ℂ)

    have char_nonzero: A_C.charpoly ≠ 0 := by
      by_contra!
      simp [A_C, Int.castRingHom] at this
      have char_monic := Matrix.charpoly_monic A_C
      simp [A_C, Int.castRingHom] at char_monic
      apply Polynomial.Monic.ne_zero at char_monic
      contradiction


    by_cases k_gt: 1 < ‖k‖
    . use k
      simp
      refine ⟨hk, k_gt⟩

    simp at k_gt
    have k_lt: ‖k‖ < 1 := by
      grind


    by_contra! eigenvalues_le_one

    have roots_prod_le: ‖A_C.charpoly.roots.prod‖ < 1 := by
      rw [Multiset.prod_eq_prod_toEnumFinset]
      rw [Complex.norm_prod]
      conv =>
        rhs
        equals ∏ i ∈ A_C.charpoly.roots.toEnumFinset, 1 =>
          simp

      apply Finset.prod_lt_prod
      .
        intro i hi
        simp at hi
        have is_root := (Polynomial.rootMultiplicity_pos (p := A_C.charpoly) ?_ (x := i.1)).mp (by omega)
        .
          by_contra!
          simp at this

          have eval_char := Matrix.eval_charpoly A_C i.1
          rw [Polynomial.IsRoot.def] at is_root
          rw [is_root] at eval_char
          simp [this] at eval_char
          rw [Matrix.det_neg] at eval_char
          simp at eval_char

          have det_nonzero :=  Matrix.det_ne_zero_of_left_inverse (A := A_C) (B := (A.inv).map (Int.castRingHom ℂ)) ?_
          . contradiction
          .
            simp [-Matrix.coe_units_inv, A_C, -Int.coe_castRingHom]
            rw [← Matrix.map_mul]
            simp
        .
          apply char_nonzero
      . intro i hi
        simp at hi
        have is_root := (Polynomial.rootMultiplicity_pos (p := A_C.charpoly) ?_ (x := i.1)).mp (by omega)
        .
          rw [← Matrix.charpoly_toLin'] at is_root
          have i_eigen := hasEigenvalue_of_isRoot_charpoly is_root
          exact eigenvalues_le_one i.1 i_eigen

        . apply char_nonzero
        -- hasEigenvalue_of_isRoot_charpoly
      .
        have k_root := Module.End.isRoot_of_hasEigenvalue hk
        have min_poly_div := Matrix.minpoly_dvd_charpoly A_C
        use (k, 0)
        simp
        refine ⟨?_, ?_⟩
        .
          refine ⟨?_, ?_⟩
          .
            exact char_nonzero
          .
            simp at k_root
            have root_char := Polynomial.IsRoot.dvd k_root min_poly_div
            simp at root_char
            exact root_char
        . norm_cast


    simp [A_C] at roots_prod_le

    have cast_det := Int.cast_det A.val (R := ℂ)
    -- TODO - this can be way simpler
    cases a_det_unit
    . rename_i det_eq_one
      apply_fun (fun a => (a: ℂ)) at det_eq_one
      rw [cast_det] at det_eq_one
      simp [A_C, Int.castRingHom] at det_eq
      rw [det_eq_one] at det_eq
      rw [← det_eq] at roots_prod_le
      norm_num at roots_prod_le
    . rename_i det_eq_neg_one
      apply_fun (fun a => (a: ℂ)) at det_eq_neg_one
      rw [cast_det] at det_eq_neg_one
      simp [A_C, Int.castRingHom] at det_eq
      rw [det_eq_neg_one] at det_eq
      rw [← det_eq] at roots_prod_le
      norm_num at roots_prod_le


set_option maxHeartbeats 1200000 in
lemma subsums_unique {d: ℕ} (A: Matrix (Fin d) (Fin d) ℂ) (φ v: (Fin d) → ℂ) (N₀ N: ℕ) (hv: ‖φ ⬝ᵥ v‖ ≠ 0) (k: ℂ) (hk: 3 ≤ ‖k‖)  (hva: A.vecMul φ = k • φ) (hn: N₀ ≤ N) (p q: Finset ℕ)
  (hp: p ⊆ Finset.Ico N₀ N) (hq: q ⊆ Finset.Ico N₀ N) (hpq: p.sum (fun k => A^k • v) = q.sum (fun k => A^k • v)):
    p = q := by

  induction N, hn using Nat.le_induction generalizing p q with
  | base =>
    simp at hp
    simp at hq
    grind
  | succ n hmn ih =>

    by_cases n_both: n ∈ p ∧ n ∈ q
    .
      have p_eq: p = (p \ {n}) ∪ {n} := by
        grind
      have q_eq: q = (q \ {n}) ∪ {n} := by
        grind
      rw [p_eq, q_eq] at hpq
      rw [Finset.sum_union] at hpq
      rw [Finset.sum_union] at hpq
      simp at hpq

      have diff_eq := ih (p \ {n}) (q \ {n}) (by
        intro c hc
        simp at hc
        have c_mem := hp hc.1
        simp
        simp at c_mem
        omega
      ) (by
        intro c hc
        simp at hc
        have c_mem := hq hc.1
        simp
        simp at c_mem
        omega
      ) hpq
      . grind
      . simp
      . simp
    .
      by_cases n_neither: n ∉ p ∧ n ∉ q
      .
        have p_eq: p = (p \ {n}) := by grind
        have q_eq: q = (q \ {n}) := by grind
        rw [p_eq, q_eq] at hpq
        have diff_eq := ih (p \ {n}) (q \ {n}) (by
          intro c hc
          simp at hc
          have c_mem := hp hc.1
          simp
          simp at c_mem
          omega
        ) (by
          intro c hc
          simp at hc
          have c_mem := hq hc.1
          simp
          simp at c_mem
          omega
        ) hpq
        grind
      .
        wlog n_mem_p: n ∈ p
        .
          have swapped := this A φ v N₀ N hv k hk hva n hmn ih q p hq hp hpq.symm (by grind) (by grind) (by grind)
          exact swapped.symm
        .
          rw [not_and_or] at n_neither
          rw [not_and_or] at n_both

          have n_mem_or: n ∈ p ∨ n ∈ q := by
            grind

          clear n_mem_or n_neither
          simp [n_mem_p] at n_both

          have n_q_diff: {n} \ q = {n} := by grind
          have data := poly_cancel A v p q hpq
          have h_sum := data.h_prime
          have p_eq: p = (p \ {n}) ∪ {n} := by grind
          nth_rw 1 [p_eq] at h_sum
          rw [Finset.union_sdiff_distrib] at h_sum
          rw [Finset.sum_union] at h_sum
          .
            simp [n_q_diff] at h_sum

            have q_diff_eq: q \ p = (q \ p) \ {n} := by
              grind

            rw [q_diff_eq] at h_sum
            rw [add_comm] at h_sum
            apply eq_add_neg_of_add_eq at h_sum


            have first_subset: (q \ p) \ {n} ⊆ Finset.Ico N₀ (n) := by
              intro a ha
              simp
              simp at ha
              have a_mem := hq ha.1.1
              simp at a_mem
              grind

            have second_subset: (p \ {n}) \ q ⊆ Finset.Ico N₀ n := by
              intro a ha
              simp
              simp at ha
              have a_mem := hp ha.1.1
              simp at a_mem
              grind

            have a_pow_le: ‖φ ⬝ᵥ (A ^ n).mulVec v‖ < ‖φ ⬝ᵥ (A ^ n).mulVec v‖ := by
              nth_rw 1 [h_sum]
              rw [← Finset.sum_indicator_subset _ first_subset]
              rw [← Finset.sum_indicator_subset _ second_subset]
              rw [← sub_eq_add_neg]
              rw [← Finset.sum_sub_distrib]
              rw [dotProduct_sum]
              grw [norm_sum_le]
              grw [Finset.sum_le_sum (g := (fun x ↦ ‖φ ⬝ᵥ (A ^ x).mulVec v‖))]
              .

                apply interval_sum_le (k := k)
                . exact hv
                . exact hk
                . exact hva

              . intro a ha
                simp [Set.indicator]
                split
                . rename_i a_mem_q
                  split
                  . rename_i a_mem_other
                    simp
                  . simp
                . split
                  . simp
                  . simp

            simp at a_pow_le
          .
            rw [Finset.disjoint_iff_ne]
            intro a ha b hb
            grind


lemma int_matrix_exponential_growth {d: ℕ} (A: (Matrix (Fin d) (Fin d) ℤ)) (φ : (Fin d) → ℂ) (v: Fin d → ℤ) (v_ne_zero: ‖φ ⬝ᵥ (Int.castRingHom ℂ) ∘ v‖ ≠ 0) (k: ℂ) (hv: (A.map (Int.castRingHom ℂ)).vecMul φ = (k • φ)) (k_gt: 1 < ‖k‖):
    ∀ N, 2^(N - ((Nat.ceil (Real.logb ‖k‖ 3)))) ≤ #((Finset.image (fun a => a.sum (fun b => (((A^((Nat.ceil (Real.logb ‖k‖ 3)))))^b.val).mulVec v)) ((Finset.Ico ((Nat.ceil (Real.logb ‖k‖ 3))) N)).attach.powerset)) := by
  have mul_v := mul_pow_exact (A.map (Int.castRingHom ℂ)) φ k hv

  have pow_le: 3 ≤ ‖k‖^(Nat.ceil (Real.logb ‖k‖ 3)) := by
    rw [Real.le_pow_iff_log_le]
    rw [← div_le_iff₀]
    .
      rw [← Real.log_div_log]
      exact Nat.le_ceil (Real.log 3 / Real.log ‖k‖)
    . apply Real.log_pos
      grind
    . simp
    . linarith

  intro N
  by_cases N_le: N ≤ Nat.ceil (Real.logb ‖k‖ 3)
  .
    simp [N_le]
    apply Finset.powerset_nonempty
  simp at N_le
  rw [Finset.card_image_of_injective]
  .
    simp
  .
    intro a b hab

    have mul_one := mul_v 1
    simp at mul_one

    have sums_eq := subsums_unique ((A.map (Int.castRingHom ℂ))^(⌈Real.logb ‖k‖ 3⌉₊)) φ ((Int.castRingHom ℂ) ∘ v) (Nat.ceil (Real.logb ‖k‖ 3)) N (by
      simpa using v_ne_zero
    ) (k^(Nat.ceil (Real.logb ‖k‖ 3))) (by simp [pow_le]) (by
      rw [mul_v]
    ) (by omega) (a.image Subtype.val) (b.image Subtype.val) ?_ ?_ ?_
    . rw [Finset.image_inj] at sums_eq
      . exact sums_eq
      . simp
    .
      intro x hx
      simp at hx
      rw [Finset.mem_Ico]
      obtain ⟨⟨le_x, other⟩, hy⟩ := hx
      refine ⟨?_, by omega⟩
      simp
      exact le_x
    .
      intro x hx
      simp at hx
      rw [Finset.mem_Ico]
      obtain ⟨⟨le_x, other⟩, hy⟩ := hx
      refine ⟨?_, by omega⟩
      simp
      exact le_x
    .
      simp at hab
      simp_rw [← Matrix.map_pow]
      simp_rw [Matrix.smul_eq_mulVec]
      rw [funext_iff]
      simp only [Finset.sum_apply]
      simp_rw [← RingHom.map_mulVec]
      simp_rw [← map_sum (g := (Int.castRingHom ℂ))]
      simp_rw [← Finset.sum_apply]
      intro x
      apply congrArg
      simp [-Finset.sum_apply]
      rw [Finset.sum_apply (a := v)]
      rw [Finset.sum_apply (a := v)]
      rw [hab]
end

section
-- module Solutions.OAIQ093_PR.MatrixSubsum
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
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

lemma exists_vector_component_nonzero {d: ℕ} (v: (Fin d) → ℂ) (hv: v ≠ 0): ∃ i, v i ≠ 0 := by
  by_contra!
  simp at hv
  rw [funext_iff] at hv
  simp [this] at hv

lemma int_matrix_poly_growth_eigenvalue_oai {d: ℕ} [NeZero d] (A: (Matrix (Fin d) (Fin d) ℤ)ˣ)
  (h_poly: ∀ k: ℂ, 1 < ‖k‖ → ∀ v: (Fin d) → ℤ, ∃ a b N_2: ℕ, (0 < a) ∧ ((Nat.ceil (Real.logb ‖k‖ 3)) < N_2) ∧ (4 * ↑b + Real.log ↑a < (Real.log 2) * (N_2 - (Nat.ceil (Real.logb ‖k‖ 3)))^((1 : ℝ) / 2)) ∧ #((Finset.image (fun a => a.sum (fun b => ((((A.val)^((Nat.ceil (Real.logb ‖k‖ 3)))))^b.val).mulVec (v))) ((Finset.Ico (Nat.ceil (Real.logb ‖k‖ 3)) N_2)).attach.powerset)) ≤ a * (N_2 - (Nat.ceil (Real.logb ‖k‖ 3)))^(2*b)):
  ∀ k : Module.End.Eigenvalues (A.val.map (Int.castRingHom ℂ)).toLin', ‖k.val‖ = 1 := by


    cases int_matrix_eigenvalue A
    .
      intro k
      rename_i eigen_norm_one
      apply eigen_norm_one k k.property
    .

      rename_i gt_one
      obtain ⟨k, hk, one_lt_k⟩ := gt_one

      have k_eigen := hk
      rw [Module.End.hasEigenvalue_iff_mem_spectrum] at k_eigen
      simp at k_eigen
      rw [spectrum.mem_iff] at k_eigen
      rw [Matrix.isUnit_iff_isUnit_det] at k_eigen
      simp at k_eigen
      rw [← Matrix.exists_vecMul_eq_zero_iff] at k_eigen
      obtain ⟨v, v_nonzero, hv⟩ := k_eigen
      rw [Matrix.vecMul_sub] at hv
      conv at hv =>
        lhs
        lhs
        equals Matrix.vecMul v (Matrix.diagonal (fun _ => k)) =>
          ext a
          simp
          rw [Matrix.algebraMap_eq_diagonal]
          rw [Matrix.vecMul_diagonal]
          simp

      simp at hv
      rw [sub_eq_zero] at hv
      obtain ⟨q, hq⟩ := exists_vector_component_nonzero v v_nonzero

      have mul_dot: (v ⬝ᵥ (A.val.map (Int.castRingHom ℂ)).mulVec q) = (k • v) ⬝ᵥ q  := by
        rw [Matrix.dotProduct_mulVec]
        simp
        rw [← hv]
        simp


      have hN := int_matrix_exponential_growth (d := d)
        (A.val) v (Pi.single q 1) (by
          simp
          conv =>
            arg 1
            lhs
            rhs
            equals Pi.single q 1 =>
              ext a
              simp [Pi.single_apply]
          simp
          exact hq
        ) k (by exact hv.symm)
        one_lt_k


      specialize h_poly k one_lt_k (Pi.single q 1)
      obtain ⟨a, b, N_2, ha, N_2_gt, N_2_diff_gt, card_le⟩ := h_poly
      specialize hN N_2
      simp at hN
      simp at card_le
      grw [card_le] at hN
      rify at hN
      rw [Real.pow_le_iff_le_log] at hN
      rw [Real.log_mul] at hN
      rw [Real.log_pow] at hN
      nth_grw 2 [Real.log_natCast_le_rpow_div (ε := (1/2))] at hN
      simp at hN
      have sub_ne: 0 ≠ (N_2 - ((Nat.ceil (Real.logb ‖k‖ 3)))) := by
        grind
      field_simp at hN
      rw [add_comm] at hN
      rw [← sub_le_iff_le_add] at hN
      rw [← div_le_iff₀] at hN
      rw [sub_div] at hN
      nth_rw 1 [mul_comm] at hN
      rw [mul_div_assoc] at hN
      rw [← Real.rpow_one_sub'] at hN
      have le_n_pow: Real.log ↑a / ↑(N_2 - (Nat.ceil (Real.logb ‖k‖ 3))) ^ ((1: ℝ) / 2) ≤ Real.log a := by
        rw [div_eq_mul_inv]
        apply mul_le_of_le_one_right
        . positivity
        . norm_num
          field_simp
          apply Real.one_le_rpow
          . simp
            grind
          . norm_num


      grw [le_n_pow] at hN
      norm_num at hN
      grw [N_2_diff_gt] at hN
      simp at hN
      rw [Nat.cast_sub] at hN
      grind
      . grind
      . grind
      . grind
      .
        positivity
      . grind
      . simp
        grind
      . norm_num
        grind
      . norm_num
      . apply mul_pos
        . simp
          exact ha
        . apply pow_pos
          rw [Nat.cast_sub]
          . simp
            grind
          . grind


open scoped Pointwise Finset
end

theorem solution : type_of% @int_matrix_poly_growth_eigenvalue_oai := @int_matrix_poly_growth_eigenvalue_oai
