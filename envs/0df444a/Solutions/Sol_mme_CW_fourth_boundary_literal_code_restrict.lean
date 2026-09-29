-- Prove2me | solution 1 for mme_CW_fourth_boundary_literal_code_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:26:23.174043+00:00
-- url     : https://prove2.me/submissions/3a14907e-aa7d-4779-9ecd-932297b416ae

import Theorems.Thm_mme_CW_fourth_tensor_eq_sum_literal_terms
import Definitions.Def_mme_CW_boundary_literal_codes
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_tensor_bridge
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.Tactic

open MME TensorProduct PiTensorProduct BigOperators Module

universe u v

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 100000

namespace MME.StothersFourth.BoundaryCode

abbrev FourthIndex (q : ℕ) : Type :=
  (Fin (q + 2) × Fin (q + 2)) × (Fin (q + 2) × Fin (q + 2))

private theorem basis_mem_cwBasisGrade
    {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V]
    {ι κ : Type*} [DecidableEq κ]
    (b : Basis ι K V) (g : ι → κ) (i : ι) :
    b i ∈ cwBasisGrade b g (g i) := by
  exact Submodule.subset_span ⟨i, rfl, rfl⟩

private def cwVec
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) (a : Fin (q + 2)) :
    CWSpace K q s :=
  match s with
  | ⟨0, _⟩ => (Pi.single a 1 : Fin (q + 2) → K)
  | ⟨1, _⟩ => (Pi.single a 1 : Fin (q + 2) → K)
  | ⟨2, _⟩ => (Pi.single a 1 : Fin (q + 2) → K)

private theorem cwLiteralTermMonomial_eq_tprod
    (K : Type u) [Field K] (q : ℕ) (t : CWLiteralTerm q) :
    cwLiteralTermMonomial K q t =
      PiTensorProduct.tprod K
        (fun s => cwVec K q s (cwLiteralTermTriple q t s)) := by
  unfold cwLiteralTermMonomial CWMonom
  congr 1
  funext s
  fin_cases s <;> rfl

private theorem cwSquareCanonicalBasis_apply
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (a b : Fin (q + 2)) :
    cwSquareCanonicalBasis K q s (a, b) =
      cwVec K q s a ⊗ₜ[K] cwVec K q s b := by
  letI : IsScalarTower K K (Fin (q + 2) → K) :=
    IsScalarTower.of_algebraMap_smul (by simp)
  fin_cases s <;>
    change (Module.Basis.tensorProduct (R := K) (S := K)
      (Pi.basisFun K (Fin (q + 2)))
      (Pi.basisFun K (Fin (q + 2)))) (a, b) = _ <;>
    rw [Module.Basis.tensorProduct_apply] <;>
    simp [cwVec, Pi.basisFun_apply]

private theorem cwFourthCanonicalBasis_apply
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (p : FourthIndex q) :
    cwFourthCanonicalBasis K q s p =
      cwSquareCanonicalBasis K q s p.1 ⊗ₜ[K]
        cwSquareCanonicalBasis K q s p.2 := by
  unfold cwFourthCanonicalBasis
  exact Module.Basis.tensorProduct_apply _ _ _ _

private theorem interchange_tprod
    {K : Type u} [Field K] {d : ℕ}
    {V W : Fin d → Type u}
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

private theorem cwFourLiteralTerm_eq_basis_tprod
    (K : Type u) [Field K] (q : ℕ)
    (t₁ t₂ t₃ t₄ : CWLiteralTerm q) :
    interchange
        (interchange (cwLiteralTermMonomial K q t₁)
          (cwLiteralTermMonomial K q t₂))
        (interchange (cwLiteralTermMonomial K q t₃)
          (cwLiteralTermMonomial K q t₄)) =
      PiTensorProduct.tprod K (fun s =>
        cwFourthCanonicalBasis K q s
          (cwFourthIndexOfLiteralTerms q t₁ t₂ t₃ t₄ s)) := by
  rw [cwLiteralTermMonomial_eq_tprod, cwLiteralTermMonomial_eq_tprod,
    cwLiteralTermMonomial_eq_tprod, cwLiteralTermMonomial_eq_tprod,
    interchange_tprod, interchange_tprod, interchange_tprod]
  congr 1
  funext s
  rw [cwFourthCanonicalBasis_apply,
    cwSquareCanonicalBasis_apply, cwSquareCanonicalBasis_apply]
  rfl

private theorem cwFourthCanonical_blockProj_basis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) (a : Fin 9)
    (p : FourthIndex q) :
    (cwFourthCanonicalGrading K q).blockProj s a
        (cwFourthCanonicalBasis K q s p) =
      if h : cwFourthPairGrade q p = a then
        ⟨cwFourthCanonicalBasis K q s p, by
          rw [← h]
          exact basis_mem_cwBasisGrade
            (cwFourthCanonicalBasis K q s) (cwFourthPairGrade q) p⟩
      else 0 := by
  split_ifs with h
  · subst a
    exact TensorObj.TypeGrading.blockProj_apply_mem
      (cwFourthCanonicalGrading K q) s (cwFourthPairGrade q p) _
      (basis_mem_cwBasisGrade
        (cwFourthCanonicalBasis K q s) (cwFourthPairGrade q) p)
  · exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (cwFourthCanonicalGrading K q) s a (cwFourthPairGrade q p)
      (Ne.symm h) _
      (basis_mem_cwBasisGrade
        (cwFourthCanonicalBasis K q s) (cwFourthPairGrade q) p)

private theorem linearMap_pair_fintype_sum
    {R I M N P : Type*} [Semiring R] [Fintype I]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] [Module R P]
    (A : N →ₗ[R] P) (B : M →ₗ[R] N) (f : I → M) :
    A (B (∑ i, f i)) = ∑ i, A (B (f i)) := by
  rw [map_sum B, map_sum A]

private theorem cwBoundaryLiteral_mode_zero
    (q : ℕ) (a : CWBoundaryLetter q) :
    cwLiteralTermTriple q (cwBoundaryLiteral q a) 0 = cwZeroIndex q := by
  rcases a with i | r
  · rfl
  · fin_cases r <;> rfl

private theorem cwBoundaryLiteral_mode_one
    (q : ℕ) (a : CWBoundaryLetter q) :
    (cwSquareCoordGrade q
        (cwLiteralTermTriple q (cwBoundaryLiteral q a) 1)).val =
      cwBoundaryWeight a := by
  rcases a with i | r
  · have hi := i.isLt
    have hine : i.val ≠ q := by omega
    simp [cwBoundaryLiteral, cwLiteralTermTriple, cwBoundaryWeight,
      cwSquareCoordGrade, cwMiddleIndex, hine]
  · fin_cases r <;>
      simp [cwBoundaryLiteral, cwLiteralTermTriple, cwBoundaryWeight,
        cwSquareCoordGrade, cwZeroIndex, cwTopIndex]

private theorem cwBoundaryLiteral_mode_two
    (q : ℕ) (a : CWBoundaryLetter q) :
    (cwSquareCoordGrade q
        (cwLiteralTermTriple q (cwBoundaryLiteral q a) 2)).val +
      cwBoundaryWeight a = 2 := by
  rcases a with i | r
  · have hi := i.isLt
    have hine : i.val ≠ q := by omega
    simp [cwBoundaryLiteral, cwLiteralTermTriple, cwBoundaryWeight,
      cwSquareCoordGrade, cwMiddleIndex, hine]
  · fin_cases r <;>
      simp [cwBoundaryLiteral, cwLiteralTermTriple, cwBoundaryWeight,
        cwSquareCoordGrade, cwZeroIndex, cwTopIndex]

private theorem cwMiddleIndex_injective (q : ℕ) :
    Function.Injective (cwMiddleIndex q) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [cwMiddleIndex] at hv
  omega

private theorem cwZeroIndex_ne_middle
    (q : ℕ) (i : Fin q) : cwZeroIndex q ≠ cwMiddleIndex q i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [cwZeroIndex, cwMiddleIndex] at hv
  omega

private theorem cwTopIndex_ne_middle
    (q : ℕ) (i : Fin q) : cwTopIndex q ≠ cwMiddleIndex q i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [cwTopIndex, cwMiddleIndex] at hv
  omega

private theorem cwZeroIndex_ne_top (q : ℕ) :
    cwZeroIndex q ≠ cwTopIndex q := by
  intro h
  have hv := congrArg Fin.val h
  simp only [cwZeroIndex, cwTopIndex] at hv
  omega

private theorem cwBoundaryLiteral_mode_one_injective (q : ℕ) :
    Function.Injective
      (fun a : CWBoundaryLetter q ↦
        cwLiteralTermTriple q (cwBoundaryLiteral q a) 1) := by
  intro a b h
  rcases a with i | r <;> rcases b with j | s
  · exact congrArg Sum.inl (cwMiddleIndex_injective q h)
  · fin_cases s
    · exact (cwZeroIndex_ne_middle q i h.symm).elim
    · exact (cwTopIndex_ne_middle q i h.symm).elim
  · fin_cases r
    · exact (cwZeroIndex_ne_middle q j h).elim
    · exact (cwTopIndex_ne_middle q j h).elim
  · fin_cases r <;> fin_cases s
    · rfl
    · exact (cwZeroIndex_ne_top q h).elim
    · exact (cwZeroIndex_ne_top q h.symm).elim
    · rfl

private theorem cwBoundaryLiteral_mode_two_injective (q : ℕ) :
    Function.Injective
      (fun a : CWBoundaryLetter q ↦
        cwLiteralTermTriple q (cwBoundaryLiteral q a) 2) := by
  intro a b h
  rcases a with i | r <;> rcases b with j | s
  · exact congrArg Sum.inl (cwMiddleIndex_injective q h)
  · fin_cases s
    · exact (cwTopIndex_ne_middle q i h.symm).elim
    · exact (cwZeroIndex_ne_middle q i h.symm).elim
  · fin_cases r
    · exact (cwTopIndex_ne_middle q j h).elim
    · exact (cwZeroIndex_ne_middle q j h).elim
  · fin_cases r <;> fin_cases s
    · rfl
    · exact (cwZeroIndex_ne_top q h.symm).elim
    · exact (cwZeroIndex_ne_top q h).elim
    · rfl

private theorem cwBoundaryLiteral_injective (q : ℕ) :
    Function.Injective (cwBoundaryLiteral q) := by
  intro a b h
  apply cwBoundaryLiteral_mode_one_injective q
  exact congrArg (fun t : CWLiteralTerm q ↦ cwLiteralTermTriple q t 1) h

private theorem cwBoundaryWordIndex_mode_one_injective (q : ℕ) :
    Function.Injective (fun w : Fin 4 → CWBoundaryLetter q ↦
      cwBoundaryWordIndex w 1) := by
  intro w z h
  apply funext
  intro r
  apply cwBoundaryLiteral_mode_one_injective q
  fin_cases r
  · exact congrArg (fun p : FourthIndex q ↦ p.1.1) h
  · exact congrArg (fun p : FourthIndex q ↦ p.1.2) h
  · exact congrArg (fun p : FourthIndex q ↦ p.2.1) h
  · exact congrArg (fun p : FourthIndex q ↦ p.2.2) h

private theorem cwBoundaryWordIndex_mode_two_injective (q : ℕ) :
    Function.Injective (fun w : Fin 4 → CWBoundaryLetter q ↦
      cwBoundaryWordIndex w 2) := by
  intro w z h
  apply funext
  intro r
  apply cwBoundaryLiteral_mode_two_injective q
  fin_cases r
  · exact congrArg (fun p : FourthIndex q ↦ p.1.1) h
  · exact congrArg (fun p : FourthIndex q ↦ p.1.2) h
  · exact congrArg (fun p : FourthIndex q ↦ p.2.1) h
  · exact congrArg (fun p : FourthIndex q ↦ p.2.2) h

private def zeroFourthIndex (q : ℕ) : FourthIndex q :=
  ((cwZeroIndex q, cwZeroIndex q), (cwZeroIndex q, cwZeroIndex q))

private theorem cwBoundaryWordIndex_mode_zero
    (q : ℕ) (w : Fin 4 → CWBoundaryLetter q) :
    cwBoundaryWordIndex w 0 = zeroFourthIndex q := by
  simp [cwBoundaryWordIndex, cwBoundaryWordLiteral, zeroFourthIndex,
    cwFourthIndexOfLiteralTerms, cwBoundaryLiteral_mode_zero]

private theorem cwBoundaryWordIndex_grade_zero
    (q : ℕ) (w : Fin 4 → CWBoundaryLetter q) :
    cwFourthPairGrade q (cwBoundaryWordIndex w 0) = 0 := by
  rw [cwBoundaryWordIndex_mode_zero]
  simp [zeroFourthIndex, cwFourthPairGrade, cwSquarePairGrade,
    cwSquareCoordGrade, cwZeroIndex]

private theorem cwBoundaryWordIndex_grade_one
    (q : ℕ) (w : Fin 4 → CWBoundaryLetter q) :
    (cwFourthPairGrade q (cwBoundaryWordIndex w 1)).val =
      cwBoundaryWordWeight w := by
  simp only [cwFourthPairGrade, cwSquarePairGrade, cwBoundaryWordIndex,
    cwFourthIndexOfLiteralTerms, cwBoundaryWordLiteral]
  rw [cwBoundaryLiteral_mode_one, cwBoundaryLiteral_mode_one,
    cwBoundaryLiteral_mode_one, cwBoundaryLiteral_mode_one]
  simp [cwBoundaryWordWeight, Fin.sum_univ_succ, Nat.add_assoc]

private theorem cwBoundaryWordIndex_grade_two
    (q : ℕ) (w : Fin 4 → CWBoundaryLetter q) :
    (cwFourthPairGrade q (cwBoundaryWordIndex w 2)).val +
      cwBoundaryWordWeight w = 8 := by
  simp only [cwFourthPairGrade, cwSquarePairGrade, cwBoundaryWordIndex,
    cwFourthIndexOfLiteralTerms, cwBoundaryWordLiteral]
  have h0 := cwBoundaryLiteral_mode_two q (w 0)
  have h1 := cwBoundaryLiteral_mode_two q (w 1)
  have h2 := cwBoundaryLiteral_mode_two q (w 2)
  have h3 := cwBoundaryLiteral_mode_two q (w 3)
  simp [cwBoundaryWordWeight, Fin.sum_univ_succ]
    at h0 h1 h2 h3 ⊢
  omega

private theorem boundaryLetter_exists_of_mode_zero
    (q : ℕ) (t : CWLiteralTerm q)
    (h : cwLiteralTermTriple q t 0 = cwZeroIndex q) :
    ∃ a : CWBoundaryLetter q, cwBoundaryLiteral q a = t := by
  rcases t with ⟨i, r⟩ | r
  · fin_cases r
    · exact ⟨Sum.inl i, rfl⟩
    · exfalso
      have hv := congrArg Fin.val h
      simp [cwLiteralTermTriple, cwMiddleIndex, cwZeroIndex] at hv
    · exfalso
      have hv := congrArg Fin.val h
      simp [cwLiteralTermTriple, cwMiddleIndex, cwZeroIndex] at hv
  · fin_cases r
    · exact ⟨Sum.inr 0, rfl⟩
    · exact ⟨Sum.inr 1, rfl⟩
    · exfalso
      have hv := congrArg Fin.val h
      simp [cwLiteralTermTriple, cwTopIndex, cwZeroIndex] at hv

private noncomputable def boundaryXVec
    (K : Type u) [Field K] (C : Type u) [Fintype C] :
    (MMObj K 1 1 (Fintype.card C)).V 0 :=
  (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1 : Fin 1 × Fin 1 → K)

private noncomputable def boundaryMMVec
    (K : Type u) [Field K] {C : Type u} [Fintype C]
    (c : C) : ∀ s : Fin 3, (MMObj K 1 1 (Fintype.card C)).V s
  | ⟨0, _⟩ =>
      boundaryXVec K C
  | ⟨1, _⟩ =>
      (Pi.single ((0 : Fin 1), Fintype.equivFin C c) 1 :
        Fin 1 × Fin (Fintype.card C) → K)
  | ⟨2, _⟩ =>
      (Pi.single (Fintype.equivFin C c, (0 : Fin 1)) 1 :
        Fin (Fintype.card C) × Fin 1 → K)

private noncomputable def boundaryBasisOutput
    (K : Type u) [Field K] (q : ℕ)
    {C : Type u} [Fintype C] [DecidableEq C]
    (enc : C ↪ (Fin 4 → CWBoundaryLetter q))
    (s : Fin 3) (p : FourthIndex q) :
    (MMObj K 1 1 (Fintype.card C)).V s :=
  match s with
  | ⟨0, _⟩ =>
      if p = zeroFourthIndex q then boundaryXVec K C else 0
  | ⟨1, _⟩ =>
      ∑ c : C, if p = cwBoundaryWordIndex (enc c) 1 then
        boundaryMMVec K c 1 else 0
  | ⟨2, _⟩ =>
      ∑ c : C, if p = cwBoundaryWordIndex (enc c) 2 then
        boundaryMMVec K c 2 else 0

private noncomputable def boundaryBasisMap
    (K : Type u) [Field K] (q : ℕ)
    {C : Type u} [Fintype C] [DecidableEq C]
    (enc : C ↪ (Fin 4 → CWBoundaryLetter q))
    (sigma : Fin 3 → Fin 9) (s : Fin 3) :
    (cwFourthCanonicalGrading K q).classOf s (sigma s) →ₗ[K]
      (MMObj K 1 1 (Fintype.card C)).V s :=
  ((cwFourthCanonicalBasis K q s).constr K
      (boundaryBasisOutput K q enc s)).comp
    ((cwFourthCanonicalGrading K q).decomp s (sigma s)).subtype

private theorem boundaryBasisMap_apply_blockProj_basis
    (K : Type u) [Field K] (q : ℕ)
    {C : Type u} [Fintype C] [DecidableEq C]
    (enc : C ↪ (Fin 4 → CWBoundaryLetter q))
    (sigma : Fin 3 → Fin 9) (s : Fin 3) (p : FourthIndex q) :
    boundaryBasisMap K q enc sigma s
        ((cwFourthCanonicalGrading K q).blockProj s (sigma s)
          (cwFourthCanonicalBasis K q s p)) =
      if cwFourthPairGrade q p = sigma s then
        boundaryBasisOutput K q enc s p
      else 0 := by
  rw [cwFourthCanonical_blockProj_basis]
  split_ifs with hgrade
  · simp [boundaryBasisMap]
  · simp [boundaryBasisMap]

private theorem boundaryBasisMap_four_literal
    (K : Type u) [Field K] (q : ℕ)
    {C : Type u} [Fintype C] [DecidableEq C]
    (enc : C ↪ (Fin 4 → CWBoundaryLetter q))
    (sigma : Fin 3 → Fin 9)
    (t₁ t₂ t₃ t₄ : CWLiteralTerm q) :
    PiTensorProduct.map (boundaryBasisMap K q enc sigma)
        (PiTensorProduct.map
          (fun s => (cwFourthCanonicalGrading K q).blockProj s (sigma s))
          (interchange
            (interchange (cwLiteralTermMonomial K q t₁)
              (cwLiteralTermMonomial K q t₂))
            (interchange (cwLiteralTermMonomial K q t₃)
              (cwLiteralTermMonomial K q t₄)))) =
      PiTensorProduct.tprod K (fun s =>
        if cwFourthPairGrade q
            (cwFourthIndexOfLiteralTerms q t₁ t₂ t₃ t₄ s) = sigma s then
          boundaryBasisOutput K q enc s
            (cwFourthIndexOfLiteralTerms q t₁ t₂ t₃ t₄ s)
        else 0) := by
  let A := PiTensorProduct.map (boundaryBasisMap K q enc sigma)
  let B := PiTensorProduct.map
    (fun s => (cwFourthCanonicalGrading K q).blockProj s (sigma s))
  calc
    _ = A (B (PiTensorProduct.tprod K (fun s =>
          cwFourthCanonicalBasis K q s
            (cwFourthIndexOfLiteralTerms q t₁ t₂ t₃ t₄ s)))) := by
      exact congrArg (fun z => A (B z))
        (cwFourLiteralTerm_eq_basis_tprod K q t₁ t₂ t₃ t₄)
    _ = _ := by
      dsimp only [A, B]
      rw [PiTensorProduct.map_tprod, PiTensorProduct.map_tprod]
      congr 1
      funext s
      exact boundaryBasisMap_apply_blockProj_basis
        K q enc sigma s _

private theorem boundaryBasisOutput_encoded
    (K : Type u) [Field K] (q : ℕ)
    {C : Type u} [Fintype C] [DecidableEq C]
    (enc : C ↪ (Fin 4 → CWBoundaryLetter q))
    (c : C) (s : Fin 3) :
    boundaryBasisOutput K q enc s (cwBoundaryWordIndex (enc c) s) =
      boundaryMMVec K c s := by
  have h1 : Function.Injective (fun a : C ↦
      cwBoundaryWordIndex (enc a) 1) :=
    (cwBoundaryWordIndex_mode_one_injective q).comp enc.injective
  have h2 : Function.Injective (fun a : C ↦
      cwBoundaryWordIndex (enc a) 2) :=
    (cwBoundaryWordIndex_mode_two_injective q).comp enc.injective
  fin_cases s
  · simp [boundaryBasisOutput, boundaryMMVec, boundaryXVec,
      cwBoundaryWordIndex_mode_zero]
    try rfl
  · change (∑ x : C,
        if cwBoundaryWordIndex (enc c) 1 = cwBoundaryWordIndex (enc x) 1 then
          boundaryMMVec K x 1 else 0) = boundaryMMVec K c 1
    simpa only [h1.eq_iff] using
      (Fintype.sum_ite_eq c (fun x : C ↦ boundaryMMVec K x 1))
  · change (∑ x : C,
        if cwBoundaryWordIndex (enc c) 2 = cwBoundaryWordIndex (enc x) 2 then
          boundaryMMVec K x 2 else 0) = boundaryMMVec K c 2
    simpa only [h2.eq_iff] using
      (Fintype.sum_ite_eq c (fun x : C ↦ boundaryMMVec K x 2))

private def boundarySigma (j : Fin 9) : Fin 3 → Fin 9 :=
  cwFourthBlockType 0 j ⟨8 - j.val, by omega⟩

private theorem boundaryWord_grade_sigma
    (q : ℕ) (j : Fin 9) (w : Fin 4 → CWBoundaryLetter q)
    (hw : cwBoundaryWordWeight w = j.val) :
    ∀ s, cwFourthPairGrade q (cwBoundaryWordIndex w s) =
      boundarySigma j s := by
  intro s
  fin_cases s
  · simpa [boundarySigma, cwFourthBlockType] using
      cwBoundaryWordIndex_grade_zero q w
  · apply Fin.ext
    simpa [boundarySigma, cwFourthBlockType, hw] using
      cwBoundaryWordIndex_grade_one q w
  · apply Fin.ext
    have hz := cwBoundaryWordIndex_grade_two q w
    simp only [boundarySigma, cwFourthBlockType]
    simp only [hw] at hz
    exact Nat.eq_sub_of_add_eq hz

private theorem boundaryMMVec_tprod
    (K : Type u) [Field K] {C : Type u} [Fintype C] (c : C) :
    PiTensorProduct.tprod K (boundaryMMVec K c) =
      MMPure K 1 1 (Fintype.card C) 0 0 (Fintype.equivFin C c) := by
  rw [MMPure]
  rfl

private theorem encoded_word_eq_of_four
    (q : ℕ) {w z : Fin 4 → CWBoundaryLetter q}
    (h0 : cwBoundaryWordLiteral w 0 = cwBoundaryWordLiteral z 0)
    (h1 : cwBoundaryWordLiteral w 1 = cwBoundaryWordLiteral z 1)
    (h2 : cwBoundaryWordLiteral w 2 = cwBoundaryWordLiteral z 2)
    (h3 : cwBoundaryWordLiteral w 3 = cwBoundaryWordLiteral z 3) :
    w = z := by
  funext r
  apply cwBoundaryLiteral_injective q
  fin_cases r
  · exact h0
  · exact h1
  · exact h2
  · exact h3

private theorem four_sum_eq_single
    {I₁ I₂ I₃ I₄ X : Type*}
    [Fintype I₁] [Fintype I₂] [Fintype I₃] [Fintype I₄]
    [DecidableEq I₁] [DecidableEq I₂] [DecidableEq I₃] [DecidableEq I₄]
    [AddCommMonoid X] (w₁ : I₁) (w₂ : I₂) (w₃ : I₃) (w₄ : I₄)
    (x : X) :
    (∑ i₄, ∑ i₃, ∑ i₂, ∑ i₁,
      if i₁ = w₁ ∧ i₂ = w₂ ∧ i₃ = w₃ ∧ i₄ = w₄ then x else 0) = x := by
  calc
    _ = ∑ i₃, ∑ i₂, ∑ i₁,
        if i₁ = w₁ ∧ i₂ = w₂ ∧ i₃ = w₃ ∧ w₄ = w₄ then x else 0 := by
      apply Fintype.sum_eq_single w₄
      intro i₄ hi₄
      apply Fintype.sum_eq_zero
      intro i₃
      apply Fintype.sum_eq_zero
      intro i₂
      apply Fintype.sum_eq_zero
      intro i₁
      simp [hi₄]
    _ = ∑ i₂, ∑ i₁,
        if i₁ = w₁ ∧ i₂ = w₂ ∧ w₃ = w₃ ∧ w₄ = w₄ then x else 0 := by
      apply Fintype.sum_eq_single w₃
      intro i₃ hi₃
      apply Fintype.sum_eq_zero
      intro i₂
      apply Fintype.sum_eq_zero
      intro i₁
      simp [hi₃]
    _ = ∑ i₁,
        if i₁ = w₁ ∧ w₂ = w₂ ∧ w₃ = w₃ ∧ w₄ = w₄ then x else 0 := by
      apply Fintype.sum_eq_single w₂
      intro i₂ hi₂
      apply Fintype.sum_eq_zero
      intro i₁
      simp [hi₂]
    _ = if w₁ = w₁ ∧ w₂ = w₂ ∧ w₃ = w₃ ∧ w₄ = w₄ then x else 0 := by
      apply Fintype.sum_eq_single w₁
      intro i₁ hi₁
      simp [hi₁]
    _ = x := by simp

private theorem four_sum_sum_comm
    {I₁ I₂ I₃ I₄ C X : Type*}
    [Fintype I₁] [Fintype I₂] [Fintype I₃] [Fintype I₄] [Fintype C]
    [AddCommMonoid X] (f : I₁ → I₂ → I₃ → I₄ → C → X) :
    (∑ i₄, ∑ i₃, ∑ i₂, ∑ i₁, ∑ c,
        f i₁ i₂ i₃ i₄ c) =
      ∑ c, ∑ i₄, ∑ i₃, ∑ i₂, ∑ i₁,
        f i₁ i₂ i₃ i₄ c := by
  calc
    _ = ∑ i₄, ∑ i₃, ∑ i₂, ∑ c, ∑ i₁,
        f i₁ i₂ i₃ i₄ c := by
      apply Finset.sum_congr rfl
      intro i₄ _
      apply Finset.sum_congr rfl
      intro i₃ _
      apply Finset.sum_congr rfl
      intro i₂ _
      exact Finset.sum_comm
    _ = ∑ i₄, ∑ i₃, ∑ c, ∑ i₂, ∑ i₁,
        f i₁ i₂ i₃ i₄ c := by
      apply Finset.sum_congr rfl
      intro i₄ _
      apply Finset.sum_congr rfl
      intro i₃ _
      exact Finset.sum_comm
    _ = ∑ i₄, ∑ c, ∑ i₃, ∑ i₂, ∑ i₁,
        f i₁ i₂ i₃ i₄ c := by
      apply Finset.sum_congr rfl
      intro i₄ _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

private theorem boundary_four_literal_image
    (K : Type u) [Field K] (q : ℕ)
    {C : Type u} [Fintype C] [DecidableEq C]
    (enc : C ↪ (Fin 4 → CWBoundaryLetter q))
    (j : Fin 9)
    (hweight : ∀ c, cwBoundaryWordWeight (enc c) = j.val)
    (t₁ t₂ t₃ t₄ : CWLiteralTerm q) :
    PiTensorProduct.map (boundaryBasisMap K q enc (boundarySigma j))
        (PiTensorProduct.map
          (fun s => (cwFourthCanonicalGrading K q).blockProj s
            (boundarySigma j s))
          (interchange
            (interchange (cwLiteralTermMonomial K q t₁)
              (cwLiteralTermMonomial K q t₂))
            (interchange (cwLiteralTermMonomial K q t₃)
              (cwLiteralTermMonomial K q t₄)))) =
      ∑ c : C,
        if t₁ = cwBoundaryWordLiteral (enc c) 0 ∧
            t₂ = cwBoundaryWordLiteral (enc c) 1 ∧
            t₃ = cwBoundaryWordLiteral (enc c) 2 ∧
            t₄ = cwBoundaryWordLiteral (enc c) 3 then
          MMPure K 1 1 (Fintype.card C) 0 0 (Fintype.equivFin C c)
        else 0 := by
  classical
  by_cases henc : ∃ c : C,
      t₁ = cwBoundaryWordLiteral (enc c) 0 ∧
      t₂ = cwBoundaryWordLiteral (enc c) 1 ∧
      t₃ = cwBoundaryWordLiteral (enc c) 2 ∧
      t₄ = cwBoundaryWordLiteral (enc c) 3
  · obtain ⟨c, hc₁, hc₂, hc₃, hc₄⟩ := henc
    subst t₁
    subst t₂
    subst t₃
    subst t₄
    refine Eq.trans (b := PiTensorProduct.tprod K (boundaryMMVec K c)) ?_ ?_
    · refine (boundaryBasisMap_four_literal K q enc (boundarySigma j)
        (cwBoundaryWordLiteral (enc c) 0) (cwBoundaryWordLiteral (enc c) 1)
        (cwBoundaryWordLiteral (enc c) 2)
        (cwBoundaryWordLiteral (enc c) 3)).trans ?_
      congr 1
      funext s
      change (if cwFourthPairGrade q (cwBoundaryWordIndex (enc c) s) =
          boundarySigma j s then
        boundaryBasisOutput K q enc s (cwBoundaryWordIndex (enc c) s)
      else 0) = boundaryMMVec K c s
      rw [if_pos (boundaryWord_grade_sigma q j (enc c) (hweight c) s)]
      exact boundaryBasisOutput_encoded K q enc c s
    refine Eq.trans (b := MMPure K 1 1 (Fintype.card C) 0 0
        (Fintype.equivFin C c)) (boundaryMMVec_tprod K c) ?_
    symm
    calc
      _ = if cwBoundaryWordLiteral (enc c) 0 =
              cwBoundaryWordLiteral (enc c) 0 ∧
            cwBoundaryWordLiteral (enc c) 1 =
              cwBoundaryWordLiteral (enc c) 1 ∧
            cwBoundaryWordLiteral (enc c) 2 =
              cwBoundaryWordLiteral (enc c) 2 ∧
            cwBoundaryWordLiteral (enc c) 3 =
              cwBoundaryWordLiteral (enc c) 3 then
          MMPure K 1 1 (Fintype.card C) 0 0
            (Fintype.equivFin C c)
        else 0 := by
          apply Fintype.sum_eq_single c
          intro c' hc'
          rw [if_neg]
          intro hfour
          apply hc'
          apply enc.injective
          exact (encoded_word_eq_of_four q
            hfour.1 hfour.2.1 hfour.2.2.1 hfour.2.2.2).symm
      _ = _ := by simp
  · have hsumzero :
        (∑ c : C,
          if t₁ = cwBoundaryWordLiteral (enc c) 0 ∧
              t₂ = cwBoundaryWordLiteral (enc c) 1 ∧
              t₃ = cwBoundaryWordLiteral (enc c) 2 ∧
              t₄ = cwBoundaryWordLiteral (enc c) 3 then
            MMPure K 1 1 (Fintype.card C) 0 0 (Fintype.equivFin C c)
          else 0) = 0 := by
      apply Fintype.sum_eq_zero
      intro c
      rw [if_neg]
      intro hc
      exact henc ⟨c, hc⟩
    rw [hsumzero]
    rw [boundaryBasisMap_four_literal]
    by_cases hzero :
        cwFourthIndexOfLiteralTerms q t₁ t₂ t₃ t₄ 0 =
          zeroFourthIndex q
    · have ht₁ : cwLiteralTermTriple q t₁ 0 = cwZeroIndex q :=
        congrArg (fun p : FourthIndex q ↦ p.1.1) hzero
      have ht₂ : cwLiteralTermTriple q t₂ 0 = cwZeroIndex q :=
        congrArg (fun p : FourthIndex q ↦ p.1.2) hzero
      have ht₃ : cwLiteralTermTriple q t₃ 0 = cwZeroIndex q :=
        congrArg (fun p : FourthIndex q ↦ p.2.1) hzero
      have ht₄ : cwLiteralTermTriple q t₄ 0 = cwZeroIndex q :=
        congrArg (fun p : FourthIndex q ↦ p.2.2) hzero
      obtain ⟨a₁, ha₁⟩ := boundaryLetter_exists_of_mode_zero q t₁ ht₁
      obtain ⟨a₂, ha₂⟩ := boundaryLetter_exists_of_mode_zero q t₂ ht₂
      obtain ⟨a₃, ha₃⟩ := boundaryLetter_exists_of_mode_zero q t₃ ht₃
      obtain ⟨a₄, ha₄⟩ := boundaryLetter_exists_of_mode_zero q t₄ ht₄
      subst t₁
      subst t₂
      subst t₃
      subst t₄
      let w : Fin 4 → CWBoundaryLetter q := ![a₁, a₂, a₃, a₄]
      have hwindex :
          cwFourthIndexOfLiteralTerms q
              (cwBoundaryLiteral q a₁) (cwBoundaryLiteral q a₂)
              (cwBoundaryLiteral q a₃) (cwBoundaryLiteral q a₄) 1 =
            cwBoundaryWordIndex w 1 := by
        rfl
      have hnotword : ∀ c : C, enc c ≠ w := by
        intro c hc
        apply henc
        refine ⟨c, ?_⟩
        rw [hc]
        exact ⟨rfl, rfl, rfl, rfl⟩
      have hout :
          boundaryBasisOutput K q enc 1 (cwBoundaryWordIndex w 1) = 0 := by
        simp only [boundaryBasisOutput]
        apply Fintype.sum_eq_zero
        intro c
        have hneq : cwBoundaryWordIndex w 1 ≠
            cwBoundaryWordIndex (enc c) 1 := by
          intro hi
          apply hnotword c
          exact (cwBoundaryWordIndex_mode_one_injective q hi).symm
        rw [if_neg hneq]
        try rfl
      apply (PiTensorProduct.tprod K).map_coord_zero (1 : Fin 3)
      by_cases hgrade :
          cwFourthPairGrade q
              (cwFourthIndexOfLiteralTerms q
                (cwBoundaryLiteral q a₁) (cwBoundaryLiteral q a₂)
                (cwBoundaryLiteral q a₃) (cwBoundaryLiteral q a₄) 1) =
            boundarySigma j 1
      · rw [if_pos hgrade, hwindex, hout]
      · rw [if_neg hgrade]
    · apply (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3)
      by_cases hgrade :
          cwFourthPairGrade q
              (cwFourthIndexOfLiteralTerms q t₁ t₂ t₃ t₄ 0) =
            boundarySigma j 0
      · rw [if_pos hgrade]
        have hout : boundaryBasisOutput K q enc 0
            (cwFourthIndexOfLiteralTerms q t₁ t₂ t₃ t₄ 0) = 0 := by
          simp only [boundaryBasisOutput]
          rw [if_neg hzero]
          try rfl
        exact hout
      · rw [if_neg hgrade]

private theorem boundary_mmpure_sum
    (K : Type u) [Field K] (C : Type u) [Fintype C] :
    (∑ c : C, MMPure K 1 1 (Fintype.card C) 0 0 (Fintype.equivFin C c)) =
      (MMObj K 1 1 (Fintype.card C)).t := by
  rw [MMObj_t, Fin.sum_univ_one, Fin.sum_univ_one]
  simpa only using
    (Equiv.sum_comp (Fintype.equivFin C)
      (fun k : Fin (Fintype.card C) ↦
        MMPure K 1 1 (Fintype.card C) 0 0 k))

private theorem boundary_blockTensor_image
    (K : Type u) [Field K] (q : ℕ)
    {C : Type u} [Fintype C] [DecidableEq C]
    (enc : C ↪ (Fin 4 → CWBoundaryLetter q))
    (j : Fin 9)
    (hweight : ∀ c, cwBoundaryWordWeight (enc c) = j.val) :
    PiTensorProduct.map (boundaryBasisMap K q enc (boundarySigma j))
        ((cwFourthCanonicalGrading K q).blockTensor (boundarySigma j)) =
      ∑ c : C,
        MMPure K 1 1 (Fintype.card C) 0 0 (Fintype.equivFin C c) := by
  classical
  change PiTensorProduct.map (boundaryBasisMap K q enc (boundarySigma j))
      (PiTensorProduct.map
        (fun s => (cwFourthCanonicalGrading K q).blockProj s
          (boundarySigma j s))
        (cwFourthObj K q).t) = _
  rw [mme_CW_fourth_tensor_eq_sum_literal_terms]
  let A := PiTensorProduct.map (boundaryBasisMap K q enc (boundarySigma j))
  let B := PiTensorProduct.map
    (fun s => (cwFourthCanonicalGrading K q).blockProj s
      (boundarySigma j s))
  let term := fun (t₁ t₂ t₃ t₄ : CWLiteralTerm q) =>
    interchange
      (interchange (cwLiteralTermMonomial K q t₁)
        (cwLiteralTermMonomial K q t₂))
      (interchange (cwLiteralTermMonomial K q t₃)
        (cwLiteralTermMonomial K q t₄))
  refine Eq.trans (b := ∑ t₄ : CWLiteralTerm q, ∑ t₃ : CWLiteralTerm q,
      ∑ t₂ : CWLiteralTerm q, ∑ t₁ : CWLiteralTerm q,
        A (B (term t₁ t₂ t₃ t₄))) ?_ ?_
  · calc
        _ = ∑ t₄ : CWLiteralTerm q,
            A (B (∑ t₃ : CWLiteralTerm q,
              ∑ t₂ : CWLiteralTerm q, ∑ t₁ : CWLiteralTerm q,
                term t₁ t₂ t₃ t₄)) :=
          linearMap_pair_fintype_sum A B _
        _ = ∑ t₄ : CWLiteralTerm q, ∑ t₃ : CWLiteralTerm q,
            A (B (∑ t₂ : CWLiteralTerm q,
              ∑ t₁ : CWLiteralTerm q, term t₁ t₂ t₃ t₄)) := by
          apply Finset.sum_congr rfl
          intro t₄ _
          exact linearMap_pair_fintype_sum A B _
        _ = ∑ t₄ : CWLiteralTerm q, ∑ t₃ : CWLiteralTerm q,
            ∑ t₂ : CWLiteralTerm q,
              A (B (∑ t₁ : CWLiteralTerm q, term t₁ t₂ t₃ t₄)) := by
          apply Finset.sum_congr rfl
          intro t₄ _
          apply Finset.sum_congr rfl
          intro t₃ _
          exact linearMap_pair_fintype_sum A B _
        _ = ∑ t₄ : CWLiteralTerm q, ∑ t₃ : CWLiteralTerm q,
            ∑ t₂ : CWLiteralTerm q, ∑ t₁ : CWLiteralTerm q,
              A (B (term t₁ t₂ t₃ t₄)) := by
          apply Finset.sum_congr rfl
          intro t₄ _
          apply Finset.sum_congr rfl
          intro t₃ _
          apply Finset.sum_congr rfl
          intro t₂ _
          exact linearMap_pair_fintype_sum A B _
  calc
    _ = ∑ t₄ : CWLiteralTerm q, ∑ t₃ : CWLiteralTerm q,
        ∑ t₂ : CWLiteralTerm q, ∑ t₁ : CWLiteralTerm q,
        ∑ c : C,
          if t₁ = cwBoundaryWordLiteral (enc c) 0 ∧
              t₂ = cwBoundaryWordLiteral (enc c) 1 ∧
              t₃ = cwBoundaryWordLiteral (enc c) 2 ∧
              t₄ = cwBoundaryWordLiteral (enc c) 3 then
            MMPure K 1 1 (Fintype.card C) 0 0 (Fintype.equivFin C c)
          else 0 := by
      simp only [A, B, term]
      apply Finset.sum_congr rfl
      intro t₄ _
      apply Finset.sum_congr rfl
      intro t₃ _
      apply Finset.sum_congr rfl
      intro t₂ _
      apply Finset.sum_congr rfl
      intro t₁ _
      exact boundary_four_literal_image K q enc j hweight t₁ t₂ t₃ t₄
    _ = ∑ c : C, ∑ t₄ : CWLiteralTerm q, ∑ t₃ : CWLiteralTerm q,
        ∑ t₂ : CWLiteralTerm q, ∑ t₁ : CWLiteralTerm q,
          if t₁ = cwBoundaryWordLiteral (enc c) 0 ∧
              t₂ = cwBoundaryWordLiteral (enc c) 1 ∧
              t₃ = cwBoundaryWordLiteral (enc c) 2 ∧
              t₄ = cwBoundaryWordLiteral (enc c) 3 then
            MMPure K 1 1 (Fintype.card C) 0 0 (Fintype.equivFin C c)
          else 0 := by
      exact four_sum_sum_comm _
    _ = ∑ c : C,
        MMPure K 1 1 (Fintype.card C) 0 0 (Fintype.equivFin C c) := by
      apply Finset.sum_congr rfl
      intro c _
      exact four_sum_eq_single
        (cwBoundaryWordLiteral (enc c) 0)
        (cwBoundaryWordLiteral (enc c) 1)
        (cwBoundaryWordLiteral (enc c) 2)
        (cwBoundaryWordLiteral (enc c) 3)
        (MMPure K 1 1 (Fintype.card C) 0 0 (Fintype.equivFin C c))

end MME.StothersFourth.BoundaryCode

open MME.StothersFourth MME.StothersFourth.BoundaryCode

/-- Any injectively encoded family of four boundary words of one fixed
mode-one weight gives a source-faithful matrix-multiplication restriction of
the corresponding grade-zero fourth-power CW constituent. -/
theorem solution
    {K : Type u} [Field K] (q : ℕ)
    {C : Type u} [Fintype C] [DecidableEq C]
    (enc : C ↪ (Fin 4 → CWBoundaryLetter q))
    (j : Fin 9)
    (hweight : ∀ c, cwBoundaryWordWeight (enc c) = j.val) :
    TensorObj.Restrict (MMObj K 1 1 (Fintype.card C))
      (cwFourthConstituent K q 0 j ⟨8 - j.val, by omega⟩) := by
  refine ⟨boundaryBasisMap K q enc (boundarySigma j), ?_⟩
  change PiTensorProduct.map (boundaryBasisMap K q enc (boundarySigma j))
      ((cwFourthCanonicalGrading K q).blockTensor (boundarySigma j)) =
    (MMObj K 1 1 (Fintype.card C)).t
  exact (boundary_blockTensor_image K q enc j hweight).trans
    (boundary_mmpure_sum K C)
