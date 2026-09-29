-- Prove2me | solution 1 for mme_stothers_phi116_four_term_projection_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:23:18.838307+00:00
-- url     : https://prove2.me/submissions/405a1046-473d-444f-af35-fd2bc12c4c39

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi116_term_expansion

open MME TensorProduct Module Filter BigOperators

universe u

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

namespace MME.StothersFourth.Phi116

set_option autoImplicit false

private theorem basis_mem_cwBasisGrade
    {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V]
    {iota kappa : Type*} [DecidableEq kappa]
    (b : Basis iota K V) (g : iota → kappa) (i : iota) :
    b i ∈ cwBasisGrade b g (g i) := by
  exact Submodule.subset_span ⟨i, rfl, rfl⟩

theorem cwPhi116ThreeGrading_blockProj_basis
    (K : Type u) [Field K] (s : Fin 3) (a : Fin 3)
    (p : Phi116ModeIndex s) :
    (cwPhi116ThreeGrading K).blockProj s a
        (phi116CanonicalBasis K s p) =
      if h : phi116OuterGrade s p = a then
        ⟨phi116CanonicalBasis K s p, by
          rw [← h]
          exact basis_mem_cwBasisGrade
            (phi116CanonicalBasis K s) (phi116OuterGrade s) p⟩
      else 0 := by
  split_ifs with h
  · subst a
    exact TensorObj.TypeGrading.blockProj_apply_mem
      (cwPhi116ThreeGrading K) s (phi116OuterGrade s p) _
      (basis_mem_cwBasisGrade
        (phi116CanonicalBasis K s) (phi116OuterGrade s) p)
  · exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (cwPhi116ThreeGrading K) s a (phi116OuterGrade s p) (Ne.symm h) _
      (basis_mem_cwBasisGrade
        (phi116CanonicalBasis K s) (phi116OuterGrade s) p)
theorem phi116_square_support_pair_classification
    (i₁ j₁ k₁ i₂ j₂ k₂ : Fin 5)
    (h₁ : i₁.val + j₁.val + k₁.val = 4)
    (h₂ : i₂.val + j₂.val + k₂.val = 4)
    (hi : i₁.val + i₂.val = 1)
    (hj : j₁.val + j₂.val = 1)
    (_hk : k₁.val + k₂.val = 6) :
    (i₁ = 0 ∧ j₁ = 1 ∧ k₁ = 3 ∧
      i₂ = 1 ∧ j₂ = 0 ∧ k₂ = 3) ∨
    (i₁ = 1 ∧ j₁ = 0 ∧ k₁ = 3 ∧
      i₂ = 0 ∧ j₂ = 1 ∧ k₂ = 3) ∨
    (i₁ = 0 ∧ j₁ = 0 ∧ k₁ = 4 ∧
      i₂ = 1 ∧ j₂ = 1 ∧ k₂ = 2) ∨
    (i₁ = 1 ∧ j₁ = 1 ∧ k₁ = 2 ∧
      i₂ = 0 ∧ j₂ = 0 ∧ k₂ = 4) := by
  simp only [Fin.ext_iff]
  omega

theorem phi116_outer_address_classification
    (i₁ j₁ k₁ i₂ j₂ k₂ : Fin 5)
    (h₁ : i₁.val + j₁.val + k₁.val = 4)
    (h₂ : i₂.val + j₂.val + k₂.val = 4)
    (hi : i₁.val + i₂.val = 1)
    (hj : j₁.val + j₂.val = 1)
    (hk : k₁.val + k₂.val = 6) :
    (fun s => phi116OuterClass s (cwSquareBlockType i₁ j₁ k₁ s)) =
        ![0, 1, 2] ∨
    (fun s => phi116OuterClass s (cwSquareBlockType i₁ j₁ k₁ s)) =
        ![1, 0, 2] ∨
    (fun s => phi116OuterClass s (cwSquareBlockType i₁ j₁ k₁ s)) =
        ![0, 0, 0] ∨
    (fun s => phi116OuterClass s (cwSquareBlockType i₁ j₁ k₁ s)) =
        ![1, 1, 1] := by
  rcases phi116_square_support_pair_classification
      i₁ j₁ k₁ i₂ j₂ k₂ h₁ h₂ hi hj hk with
    h | h | h | h
  all_goals
    rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · left
    funext s
    fin_cases s <;> rfl
  · right; left
    funext s
    fin_cases s <;> rfl
  · right; right; left
    funext s
    fin_cases s <;> rfl
  · right; right; right
    funext s
    fin_cases s <;> rfl
private theorem cwSquareCoordGrade_O (q : ℕ) :
    cwSquareCoordGrade q (cwO q) = 0 := by
  simp [cwSquareCoordGrade, cwO]

private theorem cwSquareCoordGrade_M (q : ℕ) (i : Fin q) :
    cwSquareCoordGrade q (cwM q i) = 1 := by
  simp [cwSquareCoordGrade, cwM]
  omega

private theorem cwSquareCoordGrade_T (q : ℕ) :
    cwSquareCoordGrade q (cwT q) = 2 := by
  simp [cwSquareCoordGrade, cwT]

private theorem cwSupportedTriple_grade_sum_two
    (q : ℕ) (a b c : Fin (q + 2))
    (h : cwSupportedTriple q a b c) :
    (cwSquareCoordGrade q a).val + (cwSquareCoordGrade q b).val +
      (cwSquareCoordGrade q c).val = 2 := by
  rcases h with
    ⟨i, rfl, rfl, rfl⟩ | ⟨i, rfl, rfl, rfl⟩ |
    ⟨i, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    simp [cwSquareCoordGrade_O, cwSquareCoordGrade_M,
      cwSquareCoordGrade_T]
private theorem cwTerm_supported (q : ℕ) (t : CWTerm q) :
    cwSupportedTriple q
      (cwTermTriple q t 0) (cwTermTriple q t 1) (cwTermTriple q t 2) := by
  rcases t with ⟨i, r⟩ | r <;> fin_cases r <;>
    simp [cwTermTriple, cwSupportedTriple]
private def cwVec
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) (a : Fin (q + 2)) :
    CWSpace K q s :=
  match s with
  | ⟨0, _⟩ => (Pi.single a 1 : Fin (q + 2) → K)
  | ⟨1, _⟩ => (Pi.single a 1 : Fin (q + 2) → K)
  | ⟨2, _⟩ => (Pi.single a 1 : Fin (q + 2) → K)

private theorem cwTermMonom_eq_tprod
    (K : Type u) [Field K] (q : ℕ) (t : CWTerm q) :
    cwTermMonom K q t =
      PiTensorProduct.tprod K (fun s => cwVec K q s (cwTermTriple q t s)) := by
  unfold cwTermMonom CWMonom
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
    (p :
      (Fin (q + 2) × Fin (q + 2)) ×
      (Fin (q + 2) × Fin (q + 2))) :
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
    interchange (PiTensorProduct.tprod K v) (PiTensorProduct.tprod K w) =
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
private theorem cwFourTerm_eq_basis_tprod
    (K : Type u) [Field K] (t₁ t₂ t₃ t₄ : CWTerm 6) :
    interchange
        (interchange (cwTermMonom K 6 t₁) (cwTermMonom K 6 t₂))
        (interchange (cwTermMonom K 6 t₃) (cwTermMonom K 6 t₄)) =
      PiTensorProduct.tprod K (fun s =>
        cwFourthCanonicalBasis K 6 s
          ((cwTermTriple 6 t₁ s, cwTermTriple 6 t₂ s),
           (cwTermTriple 6 t₃ s, cwTermTriple 6 t₄ s))) := by
  rw [cwTermMonom_eq_tprod, cwTermMonom_eq_tprod,
    cwTermMonom_eq_tprod, cwTermMonom_eq_tprod,
    interchange_tprod, interchange_tprod, interchange_tprod]
  congr 1
  funext s
  rw [cwFourthCanonicalBasis_apply,
    cwSquareCanonicalBasis_apply, cwSquareCanonicalBasis_apply]
  rfl

private theorem cwFourthCanonical_blockProj_basis
    (K : Type u) [Field K] (s : Fin 3) (a : Fin 9)
    (p : FourthIndex) :
    (cwFourthCanonicalGrading K 6).blockProj s a
        (cwFourthCanonicalBasis K 6 s p) =
      if h : cwFourthPairGrade 6 p = a then
        ⟨cwFourthCanonicalBasis K 6 s p, by
          rw [← h]
          exact basis_mem_cwBasisGrade
            (cwFourthCanonicalBasis K 6 s) (cwFourthPairGrade 6) p⟩
      else 0 := by
  split_ifs with h
  · subst a
    exact TensorObj.TypeGrading.blockProj_apply_mem
      (cwFourthCanonicalGrading K 6) s (cwFourthPairGrade 6 p) _
      (basis_mem_cwBasisGrade
        (cwFourthCanonicalBasis K 6 s) (cwFourthPairGrade 6) p)
  · exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (cwFourthCanonicalGrading K 6) s a (cwFourthPairGrade 6 p)
      (Ne.symm h) _
      (basis_mem_cwBasisGrade
        (cwFourthCanonicalBasis K 6 s) (cwFourthPairGrade 6) p)

private theorem cwFourthCoarse_blockProj_basis
    (K : Type u) [Field K] (s : Fin 3) (p : FourthIndex) :
    (cwFourthCanonicalGrading K 6).blockProj s (phi116ModeTotalGrade s)
        (cwFourthCanonicalBasis K 6 s p) =
      if h : cwFourthPairGrade 6 p = phi116ModeTotalGrade s then
        phi116CanonicalBasis K s ⟨p, h⟩
      else 0 := by
  rw [cwFourthCanonical_blockProj_basis]
  split_ifs with h
  · apply Subtype.ext
    exact (phi116CanonicalBasis_coe K s ⟨p, h⟩).symm
  · rfl

private def fourthIndexOfTerms
    (t₁ t₂ t₃ t₄ : CWTerm 6) (s : Fin 3) : FourthIndex :=
  ((cwTermTriple 6 t₁ s, cwTermTriple 6 t₂ s),
   (cwTermTriple 6 t₃ s, cwTermTriple 6 t₄ s))

private def firstSquareType
    (t₁ t₂ : CWTerm 6) (s : Fin 3) : Fin 5 :=
  cwSquarePairGrade 6 (cwTermTriple 6 t₁ s, cwTermTriple 6 t₂ s)

private def secondSquareType
    (t₃ t₄ : CWTerm 6) (s : Fin 3) : Fin 5 :=
  cwSquarePairGrade 6 (cwTermTriple 6 t₃ s, cwTermTriple 6 t₄ s)

private def fourTermOuterAddress
    (t₁ t₂ : CWTerm 6) : Fin 3 → Fin 3 :=
  fun s => phi116OuterClass s (firstSquareType t₁ t₂ s)

private theorem firstSquareType_grade_sum_four
    (t₁ t₂ : CWTerm 6) :
    (firstSquareType t₁ t₂ 0).val +
      (firstSquareType t₁ t₂ 1).val +
      (firstSquareType t₁ t₂ 2).val = 4 := by
  have h₁ := cwSupportedTriple_grade_sum_two 6
    (cwTermTriple 6 t₁ 0) (cwTermTriple 6 t₁ 1)
    (cwTermTriple 6 t₁ 2) (cwTerm_supported 6 t₁)
  have h₂ := cwSupportedTriple_grade_sum_two 6
    (cwTermTriple 6 t₂ 0) (cwTermTriple 6 t₂ 1)
    (cwTermTriple 6 t₂ 2) (cwTerm_supported 6 t₂)
  simp only [firstSquareType, cwSquarePairGrade]
  omega

private theorem secondSquareType_grade_sum_four
    (t₃ t₄ : CWTerm 6) :
    (secondSquareType t₃ t₄ 0).val +
      (secondSquareType t₃ t₄ 1).val +
      (secondSquareType t₃ t₄ 2).val = 4 := by
  have h₃ := cwSupportedTriple_grade_sum_two 6
    (cwTermTriple 6 t₃ 0) (cwTermTriple 6 t₃ 1)
    (cwTermTriple 6 t₃ 2) (cwTerm_supported 6 t₃)
  have h₄ := cwSupportedTriple_grade_sum_two 6
    (cwTermTriple 6 t₄ 0) (cwTermTriple 6 t₄ 1)
    (cwTermTriple 6 t₄ 2) (cwTerm_supported 6 t₄)
  simp only [secondSquareType, cwSquarePairGrade]
  omega

private theorem fourTermOuterAddress_classification
    (t₁ t₂ t₃ t₄ : CWTerm 6)
    (hcoarse : ∀ s,
      cwFourthPairGrade 6 (fourthIndexOfTerms t₁ t₂ t₃ t₄ s) =
        phi116ModeTotalGrade s) :
    fourTermOuterAddress t₁ t₂ = ![0, 1, 2] ∨
    fourTermOuterAddress t₁ t₂ = ![1, 0, 2] ∨
    fourTermOuterAddress t₁ t₂ = ![0, 0, 0] ∨
    fourTermOuterAddress t₁ t₂ = ![1, 1, 1] := by
  have hi := congrArg Fin.val (hcoarse 0)
  have hj := congrArg Fin.val (hcoarse 1)
  have hk := congrArg Fin.val (hcoarse 2)
  have h₁ := firstSquareType_grade_sum_four t₁ t₂
  have h₂ := secondSquareType_grade_sum_four t₃ t₄
  have hi' :
      (firstSquareType t₁ t₂ 0).val +
        (secondSquareType t₃ t₄ 0).val = 1 := by
    simpa [cwFourthPairGrade, fourthIndexOfTerms, firstSquareType,
      secondSquareType, phi116ModeTotalGrade, cwFourthBlockType] using hi
  have hj' :
      (firstSquareType t₁ t₂ 1).val +
        (secondSquareType t₃ t₄ 1).val = 1 := by
    simpa [cwFourthPairGrade, fourthIndexOfTerms, firstSquareType,
      secondSquareType, phi116ModeTotalGrade, cwFourthBlockType] using hj
  have hk' :
      (firstSquareType t₁ t₂ 2).val +
        (secondSquareType t₃ t₄ 2).val = 6 := by
    simpa [cwFourthPairGrade, fourthIndexOfTerms, firstSquareType,
      secondSquareType, phi116ModeTotalGrade, cwFourthBlockType] using hk
  have hclass := phi116_outer_address_classification
      (firstSquareType t₁ t₂ 0)
      (firstSquareType t₁ t₂ 1)
      (firstSquareType t₁ t₂ 2)
      (secondSquareType t₃ t₄ 0)
      (secondSquareType t₃ t₄ 1)
      (secondSquareType t₃ t₄ 2) h₁ h₂
      hi' hj' hk'
  have hfun :
      (fun s => phi116OuterClass s
        (cwSquareBlockType
          (firstSquareType t₁ t₂ 0)
          (firstSquareType t₁ t₂ 1)
          (firstSquareType t₁ t₂ 2) s)) =
        fourTermOuterAddress t₁ t₂ := by
    funext s
    fin_cases s <;> rfl
  rw [hfun] at hclass
  exact hclass

theorem phi116FourTermProjectionZero
    (K : Type u) [Field K] (sigma : Fin 3 → Fin 3)
    (h000 : sigma ≠ ![0, 0, 0])
    (h111 : sigma ≠ ![1, 1, 1])
    (h012 : sigma ≠ ![0, 1, 2])
    (h102 : sigma ≠ ![1, 0, 2])
    (t₁ t₂ t₃ t₄ : CWTerm 6) :
    PiTensorProduct.map
        (fun s => (cwPhi116ThreeGrading K).blockProj s (sigma s))
        (PiTensorProduct.map
          (fun s => (cwFourthCanonicalGrading K 6).blockProj s
            (phi116ModeTotalGrade s))
          (interchange
            (interchange (cwTermMonom K 6 t₁) (cwTermMonom K 6 t₂))
            (interchange (cwTermMonom K 6 t₃) (cwTermMonom K 6 t₄)))) = 0 := by
  let F := fun x =>
    PiTensorProduct.map
        (fun s => (cwPhi116ThreeGrading K).blockProj s (sigma s))
        (PiTensorProduct.map
          (fun s => (cwFourthCanonicalGrading K 6).blockProj s
            (phi116ModeTotalGrade s)) x)
  calc
    _ = F (PiTensorProduct.tprod K (fun s =>
          cwFourthCanonicalBasis K 6 s
            (fourthIndexOfTerms t₁ t₂ t₃ t₄ s))) := by
      exact congrArg F (cwFourTerm_eq_basis_tprod K t₁ t₂ t₃ t₄)
    _ = 0 := by
      dsimp only [F]
      rw [PiTensorProduct.map_tprod]
      erw [PiTensorProduct.map_tprod]
      by_cases hcoarse : ∀ s,
          cwFourthPairGrade 6
              (fourthIndexOfTerms t₁ t₂ t₃ t₄ s) =
            phi116ModeTotalGrade s
      · have hsupported := fourTermOuterAddress_classification
          t₁ t₂ t₃ t₄ hcoarse
        have haddress : fourTermOuterAddress t₁ t₂ ≠ sigma := by
          rcases hsupported with hs | hs | hs | hs
          · intro heq; exact h012 (heq.symm.trans hs)
          · intro heq; exact h102 (heq.symm.trans hs)
          · intro heq; exact h000 (heq.symm.trans hs)
          · intro heq; exact h111 (heq.symm.trans hs)
        have hdiff : ∃ s,
            fourTermOuterAddress t₁ t₂ s ≠ sigma s := by
          by_contra hnone
          push Not at hnone
          exact haddress (funext hnone)
        obtain ⟨s, hs⟩ := hdiff
        apply (PiTensorProduct.tprod K).map_coord_zero s
        rw [cwFourthCoarse_blockProj_basis, dif_pos (hcoarse s)]
        refine (cwPhi116ThreeGrading_blockProj_basis K s (sigma s) _).trans ?_
        rw [dif_neg]
        simpa [phi116OuterGrade, fourTermOuterAddress, firstSquareType,
          fourthIndexOfTerms] using hs
      · push Not at hcoarse
        obtain ⟨s, hs⟩ := hcoarse
        apply (PiTensorProduct.tprod K).map_coord_zero s
        rw [cwFourthCoarse_blockProj_basis, dif_neg hs]
        simp

end MME.StothersFourth.Phi116

theorem solution
    (K : Type u) [Field K] (sigma : Fin 3 → Fin 3)
    (h000 : sigma ≠ ![0, 0, 0])
    (h111 : sigma ≠ ![1, 1, 1])
    (h012 : sigma ≠ ![0, 1, 2])
    (h102 : sigma ≠ ![1, 0, 2])
    (t₁ t₂ t₃ t₄ : MME.StothersFourth.Phi116.CWTerm 6) :
    PiTensorProduct.map
        (fun s => (MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockProj s (sigma s))
        (PiTensorProduct.map
          (fun s => (MME.StothersFourth.cwFourthCanonicalGrading K 6).blockProj s
            (MME.StothersFourth.Phi116.phi116ModeTotalGrade s))
          (interchange
            (interchange (MME.StothersFourth.Phi116.cwTermMonom K 6 t₁)
              (MME.StothersFourth.Phi116.cwTermMonom K 6 t₂))
            (interchange (MME.StothersFourth.Phi116.cwTermMonom K 6 t₃)
              (MME.StothersFourth.Phi116.cwTermMonom K 6 t₄)))) = 0 := by
  exact MME.StothersFourth.Phi116.phi116FourTermProjectionZero
    K sigma h000 h111 h012 h102 t₁ t₂ t₃ t₄
