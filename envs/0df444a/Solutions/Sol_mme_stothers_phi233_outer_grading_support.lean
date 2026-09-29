-- Prove2me | solution 1 for mme_stothers_phi233_outer_grading_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:37:33.788654+00:00
-- url     : https://prove2.me/submissions/00b70f48-de95-465e-9a80-123c0beed79e

import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_outer_grading
import Definitions.Def_mme_stothers_phi233_profile_data
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_CW_fourth_literal_support_words
import Theorems.Thm_mme_CW_fourth_tensor_eq_sum_literal_terms
import Theorems.Thm_mme_stothers_phi233_square_support_pair_classification

open MME TensorProduct PiTensorProduct BigOperators Module

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

namespace MME.StothersFourth.Phi233

private theorem basis_mem_cwBasisGrade
    {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V]
    {ι κ : Type*} [DecidableEq κ]
    (b : Basis ι K V) (g : ι -> κ) (i : ι) :
    b i ∈ cwBasisGrade b g (g i) := by
  exact Submodule.subset_span ⟨i, rfl, rfl⟩

private def cwVec
    (K : Type u) [Field K] (q : Nat) (s : Fin 3) (a : Fin (q + 2)) :
    CWSpace K q s :=
  match s with
  | ⟨0, _⟩ => (Pi.single a 1 : Fin (q + 2) -> K)
  | ⟨1, _⟩ => (Pi.single a 1 : Fin (q + 2) -> K)
  | ⟨2, _⟩ => (Pi.single a 1 : Fin (q + 2) -> K)

private theorem literalTermMonomial_eq_tprod
    (K : Type u) [Field K] (q : Nat)
    (t : CWLiteralTerm q) :
    cwLiteralTermMonomial K q t =
      PiTensorProduct.tprod K
        (fun s => cwVec K q s (cwLiteralTermTriple q t s)) := by
  unfold cwLiteralTermMonomial CWMonom
  congr 1
  funext s
  fin_cases s <;> rfl

private theorem squareCanonicalBasis_apply
    (K : Type u) [Field K] (q : Nat) (s : Fin 3)
    (a b : Fin (q + 2)) :
    cwSquareCanonicalBasis K q s (a, b) =
      cwVec K q s a ⊗ₜ[K] cwVec K q s b := by
  let : IsScalarTower K K (Fin (q + 2) -> K) :=
    IsScalarTower.of_algebraMap_smul (by simp)
  fin_cases s <;>
    change (Module.Basis.tensorProduct (R := K) (S := K)
      (Pi.basisFun K (Fin (q + 2)))
      (Pi.basisFun K (Fin (q + 2)))) (a, b) = _ <;>
    rw [Module.Basis.tensorProduct_apply] <;>
    simp [cwVec, Pi.basisFun_apply]

private theorem fourthCanonicalBasis_apply
    (K : Type u) [Field K] (q : Nat) (s : Fin 3)
    (p :
      (Fin (q + 2) × Fin (q + 2)) ×
        (Fin (q + 2) × Fin (q + 2))) :
    cwFourthCanonicalBasis K q s p =
      cwSquareCanonicalBasis K q s p.1 ⊗ₜ[K]
        cwSquareCanonicalBasis K q s p.2 := by
  unfold cwFourthCanonicalBasis
  exact Module.Basis.tensorProduct_apply _ _ _ _

private theorem interchange_tprod
    {K : Type u} [Field K] {d : Nat}
    {V W : Fin d -> Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (PiTensorProduct.tprod K v)
        (PiTensorProduct.tprod K w) =
      PiTensorProduct.tprod K (fun i => v i ⊗ₜ[K] w i) := by
  show (interchange (PiTensorProduct.tprod K v))
      (PiTensorProduct.tprod K w) = _
  rw [interchange]
  change (PiTensorProduct.lift interchangeOuter
      (PiTensorProduct.tprod K v)) (PiTensorProduct.tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  change (PiTensorProduct.lift (interchangeInner v))
      (PiTensorProduct.tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

private theorem fourLiteralTerms_eq_basis_tprod
    (K : Type u) [Field K] (q : Nat)
    (t₁ t₂ t₃ t₄ : CWLiteralTerm q) :
    interchange
        (interchange (cwLiteralTermMonomial K q t₁)
          (cwLiteralTermMonomial K q t₂))
        (interchange (cwLiteralTermMonomial K q t₃)
          (cwLiteralTermMonomial K q t₄)) =
      PiTensorProduct.tprod K (fun s =>
        cwFourthCanonicalBasis K q s
          (cwFourthIndexOfLiteralTerms q t₁ t₂ t₃ t₄ s)) := by
  rw [literalTermMonomial_eq_tprod, literalTermMonomial_eq_tprod,
    literalTermMonomial_eq_tprod, literalTermMonomial_eq_tprod,
    interchange_tprod, interchange_tprod, interchange_tprod]
  congr 1
  funext s
  rw [fourthCanonicalBasis_apply,
    squareCanonicalBasis_apply, squareCanonicalBasis_apply]
  rfl

private theorem coarse_blockProj_fourth_basis
    (K : Type u) [Field K] (q : Nat) (s : Fin 3)
    (p : (Fin (q + 2) × Fin (q + 2)) ×
      (Fin (q + 2) × Fin (q + 2))) :
    (cwFourthCanonicalGrading K q).blockProj s
        (modeTotalGrade s) (cwFourthCanonicalBasis K q s p) =
      if h : cwFourthPairGrade q p = modeTotalGrade s then
        canonicalBasis K q s ⟨p, h⟩
      else 0 := by
  split_ifs with h
  · rw [TensorObj.TypeGrading.blockProj_apply_mem]
    · apply Subtype.ext
      exact (canonicalBasis_coe K q s ⟨p, h⟩).symm
    · rw [← h]
      exact basis_mem_cwBasisGrade
        (cwFourthCanonicalBasis K q s) (cwFourthPairGrade q) p
  · exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (cwFourthCanonicalGrading K q) s (modeTotalGrade s)
      (cwFourthPairGrade q p) (Ne.symm h) _
      (basis_mem_cwBasisGrade
        (cwFourthCanonicalBasis K q s) (cwFourthPairGrade q) p)

private theorem outer_blockProj_basis
    (K : Type u) [Field K] (q : Nat) (s : Fin 3) (a : Fin 5)
    (p : ModeIndex q s) :
    (outerGrading K q).blockProj s a (canonicalBasis K q s p) =
      if h : outerGrade q s p = a then
        ⟨canonicalBasis K q s p, by
          rw [← h]
          exact basis_mem_cwBasisGrade
            (canonicalBasis K q s) (outerGrade q s) p⟩
      else 0 := by
  split_ifs with h
  · subst a
    exact TensorObj.TypeGrading.blockProj_apply_mem
      (outerGrading K q) s (outerGrade q s p) _
      (basis_mem_cwBasisGrade
        (canonicalBasis K q s) (outerGrade q s) p)
  · exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (outerGrading K q) s a (outerGrade q s p) (Ne.symm h) _
      (basis_mem_cwBasisGrade
        (canonicalBasis K q s) (outerGrade q s) p)

private theorem coordGrade_zero (q : Nat) :
    cwSquareCoordGrade q (cwZeroIndex q) = 0 := by
  simp [cwSquareCoordGrade, cwZeroIndex]

private theorem coordGrade_middle (q : Nat) (i : Fin q) :
    cwSquareCoordGrade q (cwMiddleIndex q i) = 1 := by
  simp [cwSquareCoordGrade, cwMiddleIndex]
  omega

private theorem coordGrade_top (q : Nat) :
    cwSquareCoordGrade q (cwTopIndex q) = 2 := by
  simp [cwSquareCoordGrade, cwTopIndex]

private theorem literalTerm_grade_sum_two
    (q : Nat) (t : CWLiteralTerm q) :
    (cwSquareCoordGrade q (cwLiteralTermTriple q t 0)).val +
      (cwSquareCoordGrade q (cwLiteralTermTriple q t 1)).val +
      (cwSquareCoordGrade q (cwLiteralTermTriple q t 2)).val = 2 := by
  rcases t with ⟨i, r⟩ | r <;> fin_cases r <;>
    simp [cwLiteralTermTriple, coordGrade_zero,
      coordGrade_middle, coordGrade_top]

private def firstSquareType (q : Nat)
    (t₁ t₂ : CWLiteralTerm q) (s : Fin 3) : Fin 5 :=
  cwSquarePairGrade q
    (cwLiteralTermTriple q t₁ s, cwLiteralTermTriple q t₂ s)

private def secondSquareType (q : Nat)
    (t₃ t₄ : CWLiteralTerm q) (s : Fin 3) : Fin 5 :=
  cwSquarePairGrade q
    (cwLiteralTermTriple q t₃ s, cwLiteralTermTriple q t₄ s)

private theorem firstSquareType_grade_sum_four
    (q : Nat) (t₁ t₂ : CWLiteralTerm q) :
    (firstSquareType q t₁ t₂ 0).val +
      (firstSquareType q t₁ t₂ 1).val +
      (firstSquareType q t₁ t₂ 2).val = 4 := by
  have h₁ := literalTerm_grade_sum_two q t₁
  have h₂ := literalTerm_grade_sum_two q t₂
  simp only [firstSquareType, cwSquarePairGrade]
  omega

private theorem secondSquareType_grade_sum_four
    (q : Nat) (t₃ t₄ : CWLiteralTerm q) :
    (secondSquareType q t₃ t₄ 0).val +
      (secondSquareType q t₃ t₄ 1).val +
      (secondSquareType q t₃ t₄ 2).val = 4 := by
  have h₃ := literalTerm_grade_sum_two q t₃
  have h₄ := literalTerm_grade_sum_two q t₄
  simp only [secondSquareType, cwSquarePairGrade]
  omega

private theorem fourLiteralTerms_outer_pattern
    (q : Nat) (t₁ t₂ t₃ t₄ : CWLiteralTerm q)
    (hcoarse : ∀ s,
      cwFourthPairGrade q (cwFourthIndexOfLiteralTerms q t₁ t₂ t₃ t₄ s) =
        modeTotalGrade s) :
    ∃ r : Fin 10,
      (fun s => firstSquareType q t₁ t₂ s) = pattern r := by
  have hfirst := firstSquareType_grade_sum_four q t₁ t₂
  have hsecond := secondSquareType_grade_sum_four q t₃ t₄
  have hiVal := congrArg Fin.val (hcoarse 0)
  have hjVal := congrArg Fin.val (hcoarse 1)
  have hkVal := congrArg Fin.val (hcoarse 2)
  have hi : (firstSquareType q t₁ t₂ 0).val +
      (secondSquareType q t₃ t₄ 0).val = 2 := by
    simpa [firstSquareType, secondSquareType, cwFourthPairGrade,
      cwFourthIndexOfLiteralTerms, modeTotalGrade, cwFourthBlockType] using hiVal
  have hj : (firstSquareType q t₁ t₂ 1).val +
      (secondSquareType q t₃ t₄ 1).val = 3 := by
    simpa [firstSquareType, secondSquareType, cwFourthPairGrade,
      cwFourthIndexOfLiteralTerms, modeTotalGrade, cwFourthBlockType] using hjVal
  have hk : (firstSquareType q t₁ t₂ 2).val +
      (secondSquareType q t₃ t₄ 2).val = 3 := by
    simpa [firstSquareType, secondSquareType, cwFourthPairGrade,
      cwFourthIndexOfLiteralTerms, modeTotalGrade, cwFourthBlockType] using hkVal
  rcases mme_stothers_phi233_square_support_pair_classification
      (firstSquareType q t₁ t₂ 0)
      (firstSquareType q t₁ t₂ 1)
      (firstSquareType q t₁ t₂ 2)
      (secondSquareType q t₃ t₄ 0)
      (secondSquareType q t₃ t₄ 1)
      (secondSquareType q t₃ t₄ 2)
      hfirst hsecond hi hj hk with
    h | h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
  · refine ⟨0, ?_⟩
    funext s; fin_cases s <;> simp [pattern, cwSquareBlockType, h0, h1, h2]
  · refine ⟨1, ?_⟩
    funext s; fin_cases s <;> simp [pattern, cwSquareBlockType, h0, h1, h2]
  · refine ⟨2, ?_⟩
    funext s; fin_cases s <;> simp [pattern, cwSquareBlockType, h0, h1, h2]
  · refine ⟨3, ?_⟩
    funext s; fin_cases s <;> simp [pattern, cwSquareBlockType, h0, h1, h2]
  · refine ⟨4, ?_⟩
    funext s; fin_cases s <;> simp [pattern, cwSquareBlockType, h0, h1, h2]
  · refine ⟨5, ?_⟩
    funext s; fin_cases s <;> simp [pattern, cwSquareBlockType, h0, h1, h2]
  · refine ⟨6, ?_⟩
    funext s; fin_cases s <;> simp [pattern, cwSquareBlockType, h0, h1, h2]
  · refine ⟨7, ?_⟩
    funext s; fin_cases s <;> simp [pattern, cwSquareBlockType, h0, h1, h2]
  · refine ⟨8, ?_⟩
    funext s; fin_cases s <;> simp [pattern, cwSquareBlockType, h0, h1, h2]
  · refine ⟨9, ?_⟩
    funext s; fin_cases s <;> simp [pattern, cwSquareBlockType, h0, h1, h2]

private theorem projected_literal_zero_of_no_pattern
    (K : Type u) [Field K] (q : Nat)
    (sigma : Fin 3 -> Fin 5)
    (hunsupported : ∀ r : Fin 10, sigma ≠ pattern r)
    (t₁ t₂ t₃ t₄ : CWLiteralTerm q) :
    PiTensorProduct.map
        (fun s => (outerGrading K q).blockProj s (sigma s))
        (PiTensorProduct.map
          (fun s => (cwFourthCanonicalGrading K q).blockProj s
            (modeTotalGrade s))
          (interchange
            (interchange (cwLiteralTermMonomial K q t₁)
              (cwLiteralTermMonomial K q t₂))
            (interchange (cwLiteralTermMonomial K q t₃)
              (cwLiteralTermMonomial K q t₄)))) = 0 := by
  let F := fun x =>
    PiTensorProduct.map
      (fun s => (outerGrading K q).blockProj s (sigma s))
      (PiTensorProduct.map
        (fun s => (cwFourthCanonicalGrading K q).blockProj s
          (modeTotalGrade s)) x)
  calc
    _ = F (PiTensorProduct.tprod K (fun s =>
          cwFourthCanonicalBasis K q s
            (cwFourthIndexOfLiteralTerms q t₁ t₂ t₃ t₄ s))) := by
      exact congrArg F (fourLiteralTerms_eq_basis_tprod K q t₁ t₂ t₃ t₄)
    _ = 0 := by
      dsimp only [F]
      rw [PiTensorProduct.map_tprod]
      erw [PiTensorProduct.map_tprod]
      by_cases hcoarse : ∀ s,
          cwFourthPairGrade q
              (cwFourthIndexOfLiteralTerms q t₁ t₂ t₃ t₄ s) =
            modeTotalGrade s
      · obtain ⟨r, hr⟩ := fourLiteralTerms_outer_pattern
          q t₁ t₂ t₃ t₄ hcoarse
        have haddress :
            (fun s => firstSquareType q t₁ t₂ s) ≠ sigma := by
          intro heq
          exact hunsupported r (heq.symm.trans hr)
        have hdiff : ∃ s,
            firstSquareType q t₁ t₂ s ≠ sigma s := by
          by_contra hnone
          push Not at hnone
          exact haddress (funext hnone)
        obtain ⟨s, hs⟩ := hdiff
        apply (PiTensorProduct.tprod K).map_coord_zero s
        rw [coarse_blockProj_fourth_basis, dif_pos (hcoarse s)]
        refine (outer_blockProj_basis K q s (sigma s) _).trans ?_
        rw [dif_neg]
        simpa [outerGrade, firstSquareType,
          cwFourthIndexOfLiteralTerms] using hs
      · push Not at hcoarse
        obtain ⟨s, hs⟩ := hcoarse
        apply (PiTensorProduct.tprod K).map_coord_zero s
        rw [coarse_blockProj_fourth_basis, dif_neg hs]
        simp

private theorem linearMap_pair_fintype_sum
    {R I M N P : Type*} [Semiring R] [Fintype I]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] [Module R P]
    (A : N →ₗ[R] P) (B : M →ₗ[R] N) (f : I → M) :
    A (B (∑ i, f i)) = ∑ i, A (B (f i)) := by
  rw [map_sum B, map_sum A]

private theorem outer_block_zero_of_no_pattern
    (K : Type u) [Field K] (q : Nat)
    (sigma : Fin 3 -> Fin 5)
    (hunsupported : ∀ r : Fin 10, sigma ≠ pattern r) :
    (outerGrading K q).blockTensor sigma = 0 := by
  unfold TensorObj.TypeGrading.blockTensor
  change PiTensorProduct.map
      (fun s => (outerGrading K q).blockProj s (sigma s))
      (PiTensorProduct.map
        (fun s => (cwFourthCanonicalGrading K q).blockProj s
          (modeTotalGrade s))
        (cwFourthObj K q).t) = 0
  rw [mme_CW_fourth_tensor_eq_sum_literal_terms]
  let A := PiTensorProduct.map
    (fun s => (outerGrading K q).blockProj s (sigma s))
  let B := PiTensorProduct.map
    (fun s => (cwFourthCanonicalGrading K q).blockProj s
      (modeTotalGrade s))
  let f₄ := fun t₄ : CWLiteralTerm q =>
    ∑ t₃ : CWLiteralTerm q, ∑ t₂ : CWLiteralTerm q,
      ∑ t₁ : CWLiteralTerm q,
        interchange
          (interchange (cwLiteralTermMonomial K q t₁)
            (cwLiteralTermMonomial K q t₂))
          (interchange (cwLiteralTermMonomial K q t₃)
            (cwLiteralTermMonomial K q t₄))
  calc
    _ = ∑ t₄ : CWLiteralTerm q, A (B (f₄ t₄)) := by
      exact linearMap_pair_fintype_sum A B f₄
    _ = 0 := by
      apply Fintype.sum_eq_zero
      intro t₄
      let f₃ := fun t₃ : CWLiteralTerm q =>
        ∑ t₂ : CWLiteralTerm q, ∑ t₁ : CWLiteralTerm q,
          interchange
            (interchange (cwLiteralTermMonomial K q t₁)
              (cwLiteralTermMonomial K q t₂))
            (interchange (cwLiteralTermMonomial K q t₃)
              (cwLiteralTermMonomial K q t₄))
      calc
        A (B (f₄ t₄)) =
            ∑ t₃ : CWLiteralTerm q, A (B (f₃ t₃)) := by
          dsimp only [f₄]
          exact linearMap_pair_fintype_sum A B f₃
        _ = 0 := by
          apply Fintype.sum_eq_zero
          intro t₃
          let f₂ := fun t₂ : CWLiteralTerm q =>
            ∑ t₁ : CWLiteralTerm q,
              interchange
                (interchange (cwLiteralTermMonomial K q t₁)
                  (cwLiteralTermMonomial K q t₂))
                (interchange (cwLiteralTermMonomial K q t₃)
                  (cwLiteralTermMonomial K q t₄))
          calc
            A (B (f₃ t₃)) =
                ∑ t₂ : CWLiteralTerm q, A (B (f₂ t₂)) := by
              dsimp only [f₃]
              exact linearMap_pair_fintype_sum A B f₂
            _ = 0 := by
              apply Fintype.sum_eq_zero
              intro t₂
              let f₁ := fun t₁ : CWLiteralTerm q =>
                interchange
                  (interchange (cwLiteralTermMonomial K q t₁)
                    (cwLiteralTermMonomial K q t₂))
                  (interchange (cwLiteralTermMonomial K q t₃)
                    (cwLiteralTermMonomial K q t₄))
              calc
                A (B (f₂ t₂)) =
                    ∑ t₁ : CWLiteralTerm q, A (B (f₁ t₁)) := by
                  dsimp only [f₂]
                  exact linearMap_pair_fintype_sum A B f₁
                _ = 0 := by
                  apply Fintype.sum_eq_zero
                  intro t₁
                  dsimp only [A, B, f₁]
                  exact projected_literal_zero_of_no_pattern
                    K q sigma hunsupported t₁ t₂ t₃ t₄

end MME.StothersFourth.Phi233

theorem solution
    {K : Type u} [Field K] (q : Nat) (sigma : Fin 3 -> Fin 5)
    (h : (MME.StothersFourth.Phi233.outerGrading K q).blockTensor sigma ≠ 0) :
    ∃ r : Fin 10, sigma = MME.StothersFourth.Phi233.pattern r := by
  by_contra hnone
  push Not at hnone
  exact h (MME.StothersFourth.Phi233.outer_block_zero_of_no_pattern
    K q sigma hnone)
