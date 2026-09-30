-- Prove2me | solution 1 for mme_stothers_phi233_cyclic_block_supports_mixed_addresses
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:32:12.95074+00:00
-- url     : https://prove2.me/submissions/33608be5-0a56-4556-85f2-50823b8d2b7c

import Mathlib
import Definitions.Def_mme_stothers_phi233_cyclic_grading_address
import Definitions.Def_mme_stothers_phi233_outer_grading
import Definitions.Def_mme_cyclic_triple_grading
import Definitions.Def_mme_CW_fourth_literal_support_words
import Mathlib.Tactic
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Definitions.Def_mme_stothers_phi233_profile_data
import Definitions.Def_mme_TypeGrading_kron

set_option autoImplicit false

namespace Phi233SupportProof

-- Accepted source by marwahaha; submission d9fcea1d-6f9e-436f-839b-7a2e59a1692a.
namespace SupportDependency0
open _root_.MME _root_.MME.StothersFourth _root_.MME.StothersFourth.Phi233
open MME TensorObj.TypeGrading

universe u

set_option autoImplicit false

private theorem gradingOfEq_blockTensor_ne_zero_iff
    {K : Type u} [Field K] {d t : Nat}
    {A B : TensorObj K d} (h : A = B)
    (G : B.TypeGrading t) (rho : Fin d -> Fin t) :
    (mmeGradingOfEq h G).blockTensor rho ≠ 0 ↔
      G.blockTensor rho ≠ 0 := by
  subst B
  rfl

theorem mme_cyclic_triple_grading_nonzero_factors
    {K : Type u} [Field K] {T : TensorObj K 3} {t : Nat}
    (G : T.TypeGrading t)
    (rhoX rhoY rhoZ : Fin 3 -> Fin t)
    (h : (mmeCyclicTripleGrading G).blockTensor
      (mmeCyclicTripleGrade rhoX rhoY rhoZ) ≠ 0) :
    G.blockTensor rhoX ≠ 0 /\
      G.blockTensor rhoY ≠ 0 /\
      G.blockTensor rhoZ ≠ 0 := by
  have htransport :
      (mmePublicCyclicTripleGrading G).blockTensor
          (mmeCyclicTripleGrade rhoX rhoY rhoZ) ≠ 0 := by
    exact (gradingOfEq_blockTensor_ne_zero_iff
      (cyclicSymmetrization_eq_public_perm T)
      (mmePublicCyclicTripleGrading G)
      (mmeCyclicTripleGrade rhoX rhoY rhoZ)).mp h
  have hx : G.blockTensor rhoX ≠ 0 :=
    kronGrading_blockTensor_ne_zero_left G
      (kronGrading
        (permObjGrading G cyclicPerm)
        (permObjGrading G (cyclicPerm.trans cyclicPerm)))
      rhoX
      (fun i => finProdFinEquiv
        (rhoY (cyclicPerm.symm i),
          rhoZ ((cyclicPerm.trans cyclicPerm).symm i))) htransport
  have hinner := kronGrading_blockTensor_ne_zero_right G
    (kronGrading
      (permObjGrading G cyclicPerm)
      (permObjGrading G (cyclicPerm.trans cyclicPerm)))
    rhoX
    (fun i => finProdFinEquiv
      (rhoY (cyclicPerm.symm i),
        rhoZ ((cyclicPerm.trans cyclicPerm).symm i))) htransport
  have hyPerm := kronGrading_blockTensor_ne_zero_left
    (permObjGrading G cyclicPerm)
    (permObjGrading G (cyclicPerm.trans cyclicPerm))
    (fun i => rhoY (cyclicPerm.symm i))
    (fun i => rhoZ ((cyclicPerm.trans cyclicPerm).symm i)) hinner
  have hzPerm := kronGrading_blockTensor_ne_zero_right
    (permObjGrading G cyclicPerm)
    (permObjGrading G (cyclicPerm.trans cyclicPerm))
    (fun i => rhoY (cyclicPerm.symm i))
    (fun i => rhoZ ((cyclicPerm.trans cyclicPerm).symm i)) hinner
  have hy : G.blockTensor rhoY ≠ 0 := by
    intro hy0
    apply hyPerm
    rw [permObjGrading_blockTensor G cyclicPerm rhoY, hy0, map_zero]
    rfl
  have hz : G.blockTensor rhoZ ≠ 0 := by
    intro hz0
    apply hzPerm
    rw [permObjGrading_blockTensor G
      (cyclicPerm.trans cyclicPerm) rhoZ, hz0, map_zero]
    rfl
  exact ⟨hx, hy, hz⟩
end SupportDependency0
export SupportDependency0 (mme_cyclic_triple_grading_nonzero_factors)

-- Accepted source by marwahaha; submission bc553815-e021-4f25-89c2-9e7dee3b2ad0.
namespace SupportDependency1
open _root_.MME _root_.MME.StothersFourth _root_.MME.StothersFourth.Phi233
open MME BigOperators

universe u

namespace MME.StothersFourth

set_option autoImplicit false

end MME.StothersFourth

open MME.StothersFourth

/-- The defining CW tensor is exactly the sum of its `3q+3` enumerated
literal monomials. -/
theorem mme_CWTensor_eq_sum_literal_terms
    (K : Type u) [Field K] (q : ℕ) :
    CWTensor K q =
      ∑ t : CWLiteralTerm q, cwLiteralTermMonomial K q t := by
  have hM (i : Fin q) :
      (⟨i.val + 1, by omega⟩ : Fin (q + 2)) =
        ⟨1 + i.val, by omega⟩ := by
    apply Fin.ext
    change i.val + 1 = 1 + i.val
    omega
  have hT :
      (⟨q + 1, by omega⟩ : Fin (q + 2)) =
        ⟨1 + q, by omega⟩ := by
    apply Fin.ext
    change q + 1 = 1 + q
    omega
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  unfold CWTensor cwLiteralTermMonomial
  simp [cwLiteralTermTriple, Fin.sum_univ_succ,
    cwZeroIndex, cwMiddleIndex, cwTopIndex, hM, hT]
  abel
end SupportDependency1
export SupportDependency1 (mme_CWTensor_eq_sum_literal_terms)

-- Accepted source by marwahaha; submission 0426d7d9-4aaa-40e1-bd45-db550081ef36.
namespace SupportDependency2
open _root_.MME _root_.MME.StothersFourth _root_.MME.StothersFourth.Phi233
open MME TensorProduct PiTensorProduct BigOperators Module

universe u

namespace MME.StothersFourth

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

private theorem interchange_sum_right
    {K : Type u} [Field K] {d : ℕ} {ι : Type*} [Fintype ι]
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (x : PiTensorProduct K V) (f : ι → PiTensorProduct K W) :
    interchange x (∑ i, f i) = ∑ i, interchange x (f i) := by
  exact map_sum (interchange x) f Finset.univ

private theorem interchange_sum_left
    {K : Type u} [Field K] {d : ℕ} {ι : Type*} [Fintype ι]
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ι → PiTensorProduct K V) (y : PiTensorProduct K W) :
    interchange (∑ i, f i) y = ∑ i, interchange (f i) y := by
  have h :
      (interchange (∑ i, f i) :
        PiTensorProduct K W →ₗ[K]
          PiTensorProduct K (fun i => V i ⊗[K] W i)) =
        ∑ i, interchange (f i) :=
    map_sum interchange f Finset.univ
  simpa only [LinearMap.sum_apply] using congrArg (fun g => g y) h

end MME.StothersFourth

open MME.StothersFourth

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

/-- The literal fourth CW power is the fourfold finite sum of the grouped
interchanges of literal one-factor monomials. -/
theorem mme_CW_fourth_tensor_eq_sum_literal_terms
    (K : Type u) [Field K] (q : ℕ) :
    (cwFourthObj K q).t =
      ∑ t₄ : CWLiteralTerm q, ∑ t₃ : CWLiteralTerm q,
      ∑ t₂ : CWLiteralTerm q, ∑ t₁ : CWLiteralTerm q,
        interchange
          (interchange (cwLiteralTermMonomial K q t₁)
            (cwLiteralTermMonomial K q t₂))
          (interchange (cwLiteralTermMonomial K q t₃)
            (cwLiteralTermMonomial K q t₄)) := by
  unfold cwFourthObj
  dsimp only [TensorObj.kron, CWObj]
  rw [mme_CWTensor_eq_sum_literal_terms]
  simp only [MME.StothersFourth.interchange_sum_left,
    MME.StothersFourth.interchange_sum_right]
  rfl
end SupportDependency2
export SupportDependency2 (mme_CW_fourth_tensor_eq_sum_literal_terms)

-- Accepted source by marwahaha; submission 3399e3fc-fc00-413c-8c25-0cc54d8f42bb.
namespace SupportDependency3
open _root_.MME _root_.MME.StothersFourth _root_.MME.StothersFourth.Phi233
set_option autoImplicit false

theorem mme_stothers_phi233_square_support_pair_classification
    (i₁ j₁ k₁ i₂ j₂ k₂ : Fin 5)
    (h₁ : i₁.val + j₁.val + k₁.val = 4)
    (h₂ : i₂.val + j₂.val + k₂.val = 4)
    (hi : i₁.val + i₂.val = 2)
    (hj : j₁.val + j₂.val = 3)
    (hk : k₁.val + k₂.val = 3) :
    (i₁ = 0 ∧ j₁ = 1 ∧ k₁ = 3 ∧ i₂ = 2 ∧ j₂ = 2 ∧ k₂ = 0) ∨
    (i₁ = 0 ∧ j₁ = 2 ∧ k₁ = 2 ∧ i₂ = 2 ∧ j₂ = 1 ∧ k₂ = 1) ∨
    (i₁ = 0 ∧ j₁ = 3 ∧ k₁ = 1 ∧ i₂ = 2 ∧ j₂ = 0 ∧ k₂ = 2) ∨
    (i₁ = 1 ∧ j₁ = 0 ∧ k₁ = 3 ∧ i₂ = 1 ∧ j₂ = 3 ∧ k₂ = 0) ∨
    (i₁ = 1 ∧ j₁ = 1 ∧ k₁ = 2 ∧ i₂ = 1 ∧ j₂ = 2 ∧ k₂ = 1) ∨
    (i₁ = 1 ∧ j₁ = 2 ∧ k₁ = 1 ∧ i₂ = 1 ∧ j₂ = 1 ∧ k₂ = 2) ∨
    (i₁ = 1 ∧ j₁ = 3 ∧ k₁ = 0 ∧ i₂ = 1 ∧ j₂ = 0 ∧ k₂ = 3) ∨
    (i₁ = 2 ∧ j₁ = 0 ∧ k₁ = 2 ∧ i₂ = 0 ∧ j₂ = 3 ∧ k₂ = 1) ∨
    (i₁ = 2 ∧ j₁ = 1 ∧ k₁ = 1 ∧ i₂ = 0 ∧ j₂ = 2 ∧ k₂ = 2) ∨
    (i₁ = 2 ∧ j₁ = 2 ∧ k₁ = 0 ∧ i₂ = 0 ∧ j₂ = 1 ∧ k₂ = 3) := by
  have hi₁ : i₁.val ≤ 2 := by omega
  have hj₁ : j₁.val ≤ 3 := by omega
  interval_cases hi₁v : i₁.val <;> interval_cases hj₁v : j₁.val
  · omega
  · left; simp only [Fin.ext_iff]; omega
  · right; left; simp only [Fin.ext_iff]; omega
  · right; right; left; simp only [Fin.ext_iff]; omega
  · right; right; right; left; simp only [Fin.ext_iff]; omega
  · right; right; right; right; left; simp only [Fin.ext_iff]; omega
  · right; right; right; right; right; left; simp only [Fin.ext_iff]; omega
  · right; right; right; right; right; right; left; simp only [Fin.ext_iff]; omega
  · right; right; right; right; right; right; right; left; simp only [Fin.ext_iff]; omega
  · right; right; right; right; right; right; right; right; left; simp only [Fin.ext_iff]; omega
  · right; right; right; right; right; right; right; right; right; simp only [Fin.ext_iff]; omega
  · omega
end SupportDependency3
export SupportDependency3 (mme_stothers_phi233_square_support_pair_classification)

-- Accepted source by marwahaha; submission 00b70f48-de95-465e-9a80-123c0beed79e.
namespace SupportDependency4
open _root_.MME _root_.MME.StothersFourth _root_.MME.StothersFourth.Phi233
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

theorem mme_stothers_phi233_outer_grading_support
    {K : Type u} [Field K] (q : Nat) (sigma : Fin 3 -> Fin 5)
    (h : (MME.StothersFourth.Phi233.outerGrading K q).blockTensor sigma ≠ 0) :
    ∃ r : Fin 10, sigma = MME.StothersFourth.Phi233.pattern r := by
  by_contra hnone
  push Not at hnone
  exact h (MME.StothersFourth.Phi233.outer_block_zero_of_no_pattern
    K q sigma hnone)
end SupportDependency4
export SupportDependency4 (mme_stothers_phi233_outer_grading_support)

open _root_.MME _root_.MME.StothersFourth.Phi233
universe u

theorem target
    {K : Type u} [Field K] (q : ℕ)
    {N alpha beta gamma delta : ℕ}
    (es : Fin 3 → MME.StothersFourth.Phi233.CyclicAmbientEdge
      N alpha beta gamma delta)
    (hblocks : ∀ j : Fin (2 * N),
      (mmeCyclicTripleGrading
        (MME.StothersFourth.Phi233.outerGrading K q)).blockTensor
        (fun i ↦
          MME.StothersFourth.Phi233.cyclicGradingAddress (es i) i j) ≠ 0) :
    MME.StothersFourth.Phi233.CyclicCoordinatewiseSupported
      (es 0) (es 1) (es 2) := by
  have factors (j : Fin (2 * N)) :
      (outerGrading K q).blockTensor
          (addressType (mixedAddress (es 0).1 (es 1).1 (es 2).1) j) ≠ 0 ∧
      (outerGrading K q).blockTensor
          (addressType (mixedAddress (es 1).2.1 (es 2).2.1 (es 0).2.1) j) ≠ 0 ∧
      (outerGrading K q).blockTensor
          (addressType (mixedAddress (es 2).2.2 (es 0).2.2 (es 1).2.2) j) ≠ 0 := by
    have hgrade :
        (fun i => cyclicGradingAddress (es i) i j) =
          mmeCyclicTripleGrade
            (addressType (mixedAddress (es 0).1 (es 1).1 (es 2).1) j)
            (addressType (mixedAddress (es 1).2.1 (es 2).2.1 (es 0).2.1) j)
            (addressType (mixedAddress (es 2).2.2 (es 0).2.2 (es 1).2.2) j) := by
      funext i
      fin_cases i <;> rfl
    have hnonzero := Eq.mp
      (congrArg (fun rho =>
        (mmeCyclicTripleGrading (outerGrading K q)).blockTensor rho ≠ 0) hgrade)
      (hblocks j)
    exact mme_cyclic_triple_grading_nonzero_factors
      (outerGrading K q) _ _ _ hnonzero
  exact ⟨fun j => mme_stothers_phi233_outer_grading_support q _ (factors j).1,
    fun j => mme_stothers_phi233_outer_grading_support q _ (factors j).2.1,
    fun j => mme_stothers_phi233_outer_grading_support q _ (factors j).2.2⟩

end Phi233SupportProof

open MME
universe support_u

theorem solution
    {K : Type support_u} [Field K] (q : ℕ)
    {N alpha beta gamma delta : ℕ}
    (es : Fin 3 → MME.StothersFourth.Phi233.CyclicAmbientEdge
      N alpha beta gamma delta)
    (hblocks : ∀ j : Fin (2 * N),
      (mmeCyclicTripleGrading
        (MME.StothersFourth.Phi233.outerGrading K q)).blockTensor
        (fun i ↦
          MME.StothersFourth.Phi233.cyclicGradingAddress (es i) i j) ≠ 0) :
    MME.StothersFourth.Phi233.CyclicCoordinatewiseSupported
      (es 0) (es 1) (es 2) := by
  exact Phi233SupportProof.target q es hblocks

#print axioms solution
