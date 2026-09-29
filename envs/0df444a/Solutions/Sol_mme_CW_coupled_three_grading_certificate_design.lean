-- Prove2me | solution 1 for mme_CW_coupled_three_grading_certificate_design
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T04:24:25.352094+00:00
-- url     : https://prove2.me/submissions/2f6f151c-c82b-403e-95da-b374b47aadf4

import Definitions.Def_mme_CW_square_canonical_grading
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_block_subtensor
import Mathlib.Tactic

open MME PiTensorProduct BigOperators DirectSum Module

universe u

set_option maxHeartbeats 800000

namespace CoupledThreeGrading

/-! The coordinate set in each of the three modes of the coupled tensor. -/
@[reducible] def Coord (q : ℕ) : Fin 3 → Type
  | ⟨0, _⟩ => Fin q ⊕ Fin q
  | ⟨1, _⟩ => Fin q ⊕ Fin q
  | ⟨2, _⟩ => Fin 2 ⊕ (Fin q × Fin q)

/-! The source-faithful grading: the two copies in modes zero and one
have grades zero and one; the two distinguished coordinates in mode two
have grades zero and one, while the `q × q` coordinates have grade two. -/
def coordGrade (q : ℕ) : ∀ s : Fin 3, Coord q s → Fin 3
  | ⟨0, _⟩, Sum.inl _ => 0
  | ⟨0, _⟩, Sum.inr _ => 1
  | ⟨1, _⟩, Sum.inl _ => 0
  | ⟨1, _⟩, Sum.inr _ => 1
  | ⟨2, _⟩, Sum.inl a => ⟨a.val, by omega⟩
  | ⟨2, _⟩, Sum.inr _ => 2

private instance coordFinite (q : ℕ) (s : Fin 3) : Finite (Coord q s) :=
  match s with
  | ⟨0, _⟩ => inferInstanceAs (Finite (Fin q ⊕ Fin q))
  | ⟨1, _⟩ => inferInstanceAs (Finite (Fin q ⊕ Fin q))
  | ⟨2, _⟩ => inferInstanceAs (Finite (Fin 2 ⊕ (Fin q × Fin q)))

private instance coordDecidableEq (q : ℕ) (s : Fin 3) :
    DecidableEq (Coord q s) :=
  match s with
  | ⟨0, _⟩ => inferInstanceAs (DecidableEq (Fin q ⊕ Fin q))
  | ⟨1, _⟩ => inferInstanceAs (DecidableEq (Fin q ⊕ Fin q))
  | ⟨2, _⟩ => inferInstanceAs (DecidableEq (Fin 2 ⊕ (Fin q × Fin q)))

noncomputable def coordBasis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) :
    Basis (Coord q s) K (CoupledSpace K q s) := by
  exact match s with
    | ⟨0, _⟩ => Pi.basisFun K (Fin q ⊕ Fin q)
    | ⟨1, _⟩ => Pi.basisFun K (Fin q ⊕ Fin q)
    | ⟨2, _⟩ => Pi.basisFun K (Fin 2 ⊕ (Fin q × Fin q))

noncomputable def grading
    (K : Type u) [Field K] (q : ℕ) :
    (coupledObj K q).TypeGrading 3 where
  decomp s := cwBasisGrade (coordBasis K q s) (coordGrade q s)
  is_internal s := cwBasisGrade_isInternal
    (coordBasis K q s) (coordGrade q s)

private lemma basis_mem_grade
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) (a : Coord q s) :
    coordBasis K q s a ∈
      (grading K q).decomp s (coordGrade q s a) := by
  exact Submodule.subset_span ⟨a, rfl, rfl⟩

private lemma blockProj_apply_mem
    {K : Type u} [Field K] {d t : ℕ} {T : TensorObj K d}
    (G : T.TypeGrading t) (s : Fin d) (a : Fin t)
    (x : T.V s) (hx : x ∈ G.decomp s a) :
    G.blockProj s a x = ⟨x, hx⟩ := by
  unfold TensorObj.TypeGrading.blockProj TensorObj.TypeGrading.modeLequiv
  apply Subtype.ext
  simp only [LinearMap.comp_apply]
  rw [← DirectSum.apply_eq_component]
  exact congrArg Subtype.val
    ((G.is_internal s).ofBijective_coeLinearMap_of_mem hx)

private lemma blockProj_apply_mem_ne
    {K : Type u} [Field K] {d t : ℕ} {T : TensorObj K d}
    (G : T.TypeGrading t) (s : Fin d) (a b : Fin t) (hab : a ≠ b)
    (x : T.V s) (hx : x ∈ G.decomp s b) :
    G.blockProj s a x = 0 := by
  unfold TensorObj.TypeGrading.blockProj TensorObj.TypeGrading.modeLequiv
  simp only [LinearMap.comp_apply]
  rw [← DirectSum.apply_eq_component]
  exact (G.is_internal s).ofBijective_coeLinearMap_of_mem_ne hab.symm hx

private lemma blockProj_basis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (a : Fin 3) (i : Coord q s) :
    (grading K q).blockProj s a (coordBasis K q s i) =
      if h : coordGrade q s i = a then
        ⟨coordBasis K q s i, by rw [← h]; exact basis_mem_grade K q s i⟩
      else 0 := by
  split_ifs with h
  · subst a
    exact blockProj_apply_mem (grading K q) s _ _
      (basis_mem_grade K q s i)
  · exact blockProj_apply_mem_ne (grading K q) s a _ (Ne.symm h) _
      (basis_mem_grade K q s i)

private lemma coordBasis_apply_zero
    (K : Type u) [Field K] (q : ℕ) (i : Fin q ⊕ Fin q) :
    coordBasis K q (0 : Fin 3) i = Pi.single i 1 := by
  classical
  change (Pi.basisFun K (Fin q ⊕ Fin q)) i = Pi.single i 1
  exact Pi.basisFun_apply K _ i

private lemma coordBasis_apply_one
    (K : Type u) [Field K] (q : ℕ) (i : Fin q ⊕ Fin q) :
    coordBasis K q (1 : Fin 3) i = Pi.single i 1 := by
  classical
  change (Pi.basisFun K (Fin q ⊕ Fin q)) i = Pi.single i 1
  exact Pi.basisFun_apply K _ i

private lemma coordBasis_apply_two
    (K : Type u) [Field K] (q : ℕ) (i : Fin 2 ⊕ (Fin q × Fin q)) :
    coordBasis K q (2 : Fin 3) i = Pi.single i 1 := by
  classical
  change (Pi.basisFun K (Fin 2 ⊕ (Fin q × Fin q))) i = Pi.single i 1
  exact Pi.basisFun_apply K _ i

private def blockType (a b c : Fin 3) : Fin 3 → Fin 3
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c

private def term000 (q : ℕ) (i : Fin q) : ∀ s : Fin 3, Coord q s
  | ⟨0, _⟩ => Sum.inl i
  | ⟨1, _⟩ => Sum.inl i
  | ⟨2, _⟩ => Sum.inl 0

private def term111 (q : ℕ) (k : Fin q) : ∀ s : Fin 3, Coord q s
  | ⟨0, _⟩ => Sum.inr k
  | ⟨1, _⟩ => Sum.inr k
  | ⟨2, _⟩ => Sum.inl 1

private def term012 (q : ℕ) (i k : Fin q) : ∀ s : Fin 3, Coord q s
  | ⟨0, _⟩ => Sum.inl i
  | ⟨1, _⟩ => Sum.inr k
  | ⟨2, _⟩ => Sum.inr (i, k)

private def term102 (q : ℕ) (i k : Fin q) : ∀ s : Fin 3, Coord q s
  | ⟨0, _⟩ => Sum.inr k
  | ⟨1, _⟩ => Sum.inl i
  | ⟨2, _⟩ => Sum.inr (i, k)

private noncomputable def raw000
    (K : Type u) [Field K] (q : ℕ) (i : Fin q) :
    PiTensorProduct K (CoupledSpace K q) :=
  tprod K (fun s =>
    match s with
    | ⟨0, _⟩ => (Pi.single (Sum.inl i) 1 : (Fin q ⊕ Fin q) → K)
    | ⟨1, _⟩ => (Pi.single (Sum.inl i) 1 : (Fin q ⊕ Fin q) → K)
    | ⟨2, _⟩ => (Pi.single (Sum.inl (0 : Fin 2)) 1 :
        (Fin 2 ⊕ (Fin q × Fin q)) → K))

private noncomputable def raw111
    (K : Type u) [Field K] (q : ℕ) (k : Fin q) :
    PiTensorProduct K (CoupledSpace K q) :=
  tprod K (fun s =>
    match s with
    | ⟨0, _⟩ => (Pi.single (Sum.inr k) 1 : (Fin q ⊕ Fin q) → K)
    | ⟨1, _⟩ => (Pi.single (Sum.inr k) 1 : (Fin q ⊕ Fin q) → K)
    | ⟨2, _⟩ => (Pi.single (Sum.inl (1 : Fin 2)) 1 :
        (Fin 2 ⊕ (Fin q × Fin q)) → K))

private noncomputable def raw012
    (K : Type u) [Field K] (q : ℕ) (i k : Fin q) :
    PiTensorProduct K (CoupledSpace K q) :=
  tprod K (fun s =>
    match s with
    | ⟨0, _⟩ => (Pi.single (Sum.inl i) 1 : (Fin q ⊕ Fin q) → K)
    | ⟨1, _⟩ => (Pi.single (Sum.inr k) 1 : (Fin q ⊕ Fin q) → K)
    | ⟨2, _⟩ => (Pi.single (Sum.inr (i, k)) 1 :
        (Fin 2 ⊕ (Fin q × Fin q)) → K))

private noncomputable def raw102
    (K : Type u) [Field K] (q : ℕ) (i k : Fin q) :
    PiTensorProduct K (CoupledSpace K q) :=
  tprod K (fun s =>
    match s with
    | ⟨0, _⟩ => (Pi.single (Sum.inr k) 1 : (Fin q ⊕ Fin q) → K)
    | ⟨1, _⟩ => (Pi.single (Sum.inl i) 1 : (Fin q ⊕ Fin q) → K)
    | ⟨2, _⟩ => (Pi.single (Sum.inr (i, k)) 1 :
        (Fin 2 ⊕ (Fin q × Fin q)) → K))

private lemma term000_grade (q : ℕ) (i : Fin q) :
    (fun s => coordGrade q s (term000 q i s)) = blockType 0 0 0 := by
  funext s
  fin_cases s <;> rfl

private lemma term111_grade (q : ℕ) (k : Fin q) :
    (fun s => coordGrade q s (term111 q k s)) = blockType 1 1 1 := by
  funext s
  fin_cases s <;> rfl

private lemma term012_grade (q : ℕ) (i k : Fin q) :
    (fun s => coordGrade q s (term012 q i k s)) = blockType 0 1 2 := by
  funext s
  fin_cases s <;> rfl

private lemma term102_grade (q : ℕ) (i k : Fin q) :
    (fun s => coordGrade q s (term102 q i k s)) = blockType 1 0 2 := by
  funext s
  fin_cases s <;> rfl

private lemma map_basis_tprod_zero_of_grade_ne
    (K : Type u) [Field K] (q : ℕ)
    (sigma : Fin 3 → Fin 3) (idx : ∀ s : Fin 3, Coord q s)
    (hne : (fun s => coordGrade q s (idx s)) ≠ sigma) :
    PiTensorProduct.map
        (fun s => (grading K q).blockProj s (sigma s))
        (tprod K (fun s => coordBasis K q s (idx s))) = 0 := by
  classical
  have hex : ∃ s, coordGrade q s (idx s) ≠ sigma s := Function.ne_iff.mp hne
  rcases hex with ⟨s, hs⟩
  erw [PiTensorProduct.map_tprod]
  apply MultilinearMap.map_coord_zero (tprod K) s
  exact blockProj_apply_mem_ne (grading K q) s (sigma s)
    (coordGrade q s (idx s)) hs.symm _ (basis_mem_grade K q s (idx s))

private lemma coupledTensor_as_four_basis_sums
    (K : Type u) [Field K] (q : ℕ) :
    coupledTensor K q =
      (∑ i : Fin q, tprod K (fun s => coordBasis K q s (term000 q i s))) +
      (∑ k : Fin q, tprod K (fun s => coordBasis K q s (term111 q k s))) +
      (∑ i : Fin q, ∑ k : Fin q,
        tprod K (fun s => coordBasis K q s (term012 q i k s))) +
      (∑ i : Fin q, ∑ k : Fin q,
        tprod K (fun s => coordBasis K q s (term102 q i k s))) := by
  change
    ((∑ i : Fin q, raw000 K q i) +
     (∑ k : Fin q, raw111 K q k) +
     (∑ i : Fin q, ∑ k : Fin q, raw012 K q i k) +
     (∑ i : Fin q, ∑ k : Fin q, raw102 K q i k)) = _
  have h000 (i : Fin q) :
      tprod K (fun s => coordBasis K q s (term000 q i s)) = raw000 K q i := by
    unfold raw000
    congr 1
    funext s
    fin_cases s
    · exact coordBasis_apply_zero K q (Sum.inl i)
    · exact coordBasis_apply_one K q (Sum.inl i)
    · exact coordBasis_apply_two K q (Sum.inl 0)
  have h111 (k : Fin q) :
      tprod K (fun s => coordBasis K q s (term111 q k s)) = raw111 K q k := by
    unfold raw111
    congr 1
    funext s
    fin_cases s
    · exact coordBasis_apply_zero K q (Sum.inr k)
    · exact coordBasis_apply_one K q (Sum.inr k)
    · exact coordBasis_apply_two K q (Sum.inl 1)
  have h012 (i k : Fin q) :
      tprod K (fun s => coordBasis K q s (term012 q i k s)) = raw012 K q i k := by
    unfold raw012
    congr 1
    funext s
    fin_cases s
    · exact coordBasis_apply_zero K q (Sum.inl i)
    · exact coordBasis_apply_one K q (Sum.inr k)
    · exact coordBasis_apply_two K q (Sum.inr (i, k))
  have h102 (i k : Fin q) :
      tprod K (fun s => coordBasis K q s (term102 q i k s)) = raw102 K q i k := by
    unfold raw102
    congr 1
    funext s
    fin_cases s
    · exact coordBasis_apply_zero K q (Sum.inr k)
    · exact coordBasis_apply_one K q (Sum.inl i)
    · exact coordBasis_apply_two K q (Sum.inr (i, k))
  simp_rw [h000, h111, h012, h102]

theorem support
    (K : Type u) [Field K] (q : ℕ)
    (sigma : Fin 3 → Fin 3)
    (h000 : sigma ≠ ![0, 0, 0])
    (h111 : sigma ≠ ![1, 1, 1])
    (h012 : sigma ≠ ![0, 1, 2])
    (h102 : sigma ≠ ![1, 0, 2]) :
    (grading K q).blockTensor sigma = 0 := by
  change PiTensorProduct.map
      (fun s => (grading K q).blockProj s (sigma s))
      (coupledTensor K q) = 0
  rw [coupledTensor_as_four_basis_sums]
  have hb000 : blockType 0 0 0 = ![0, 0, 0] := by
    funext s; fin_cases s <;> rfl
  have hb111 : blockType 1 1 1 = ![1, 1, 1] := by
    funext s; fin_cases s <;> rfl
  have hb012 : blockType 0 1 2 = ![0, 1, 2] := by
    funext s; fin_cases s <;> rfl
  have hb102 : blockType 1 0 2 = ![1, 0, 2] := by
    funext s; fin_cases s <;> rfl
  have hz000 (i : Fin q) :
      PiTensorProduct.map
          (fun s => (grading K q).blockProj s (sigma s))
          (tprod K (fun s => coordBasis K q s (term000 q i s))) = 0 := by
    apply map_basis_tprod_zero_of_grade_ne
    rw [term000_grade, hb000]
    exact Ne.symm h000
  have hz111 (k : Fin q) :
      PiTensorProduct.map
          (fun s => (grading K q).blockProj s (sigma s))
          (tprod K (fun s => coordBasis K q s (term111 q k s))) = 0 := by
    apply map_basis_tprod_zero_of_grade_ne
    rw [term111_grade, hb111]
    exact Ne.symm h111
  have hz012 (i k : Fin q) :
      PiTensorProduct.map
          (fun s => (grading K q).blockProj s (sigma s))
          (tprod K (fun s => coordBasis K q s (term012 q i k s))) = 0 := by
    apply map_basis_tprod_zero_of_grade_ne
    rw [term012_grade, hb012]
    exact Ne.symm h012
  have hz102 (i k : Fin q) :
      PiTensorProduct.map
          (fun s => (grading K q).blockProj s (sigma s))
          (tprod K (fun s => coordBasis K q s (term102 q i k s))) = 0 := by
    apply map_basis_tprod_zero_of_grade_ne
    rw [term102_grade, hb102]
    exact Ne.symm h102
  let F := PiTensorProduct.map
    (fun s => (grading K q).blockProj s (sigma s))
  let A := ∑ i : Fin q,
    tprod K (fun s => coordBasis K q s (term000 q i s))
  let B := ∑ k : Fin q,
    tprod K (fun s => coordBasis K q s (term111 q k s))
  let C := ∑ i : Fin q, ∑ k : Fin q,
    tprod K (fun s => coordBasis K q s (term012 q i k s))
  let D := ∑ i : Fin q, ∑ k : Fin q,
    tprod K (fun s => coordBasis K q s (term102 q i k s))
  change F (((A + B) + C) + D) = 0
  have hA : F A = 0 := by
    calc
      F A = ∑ i : Fin q,
          F (tprod K (fun s => coordBasis K q s (term000 q i s))) := by
        exact map_sum F _ Finset.univ
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        dsimp [F]
        exact hz000 i
  have hB : F B = 0 := by
    calc
      F B = ∑ k : Fin q,
          F (tprod K (fun s => coordBasis K q s (term111 q k s))) := by
        exact map_sum F _ Finset.univ
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        dsimp [F]
        exact hz111 k
  have hC : F C = 0 := by
    calc
      F C = ∑ i : Fin q, ∑ k : Fin q,
          F (tprod K (fun s => coordBasis K q s (term012 q i k s))) := by
        calc
          _ = ∑ i : Fin q, F (∑ k : Fin q,
              tprod K (fun s => coordBasis K q s (term012 q i k s))) :=
            map_sum F _ Finset.univ
          _ = _ := by
            apply Finset.sum_congr rfl
            intro i hi
            exact map_sum F _ Finset.univ
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        apply Finset.sum_eq_zero
        intro k hk
        dsimp [F]
        exact hz012 i k
  have hD : F D = 0 := by
    calc
      F D = ∑ i : Fin q, ∑ k : Fin q,
          F (tprod K (fun s => coordBasis K q s (term102 q i k s))) := by
        calc
          _ = ∑ i : Fin q, F (∑ k : Fin q,
              tprod K (fun s => coordBasis K q s (term102 q i k s))) :=
            map_sum F _ Finset.univ
          _ = _ := by
            apply Finset.sum_congr rfl
            intro i hi
            exact map_sum F _ Finset.univ
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        apply Finset.sum_eq_zero
        intro k hk
        dsimp [F]
        exact hz102 i k
  calc
    F (((A + B) + C) + D) = F ((A + B) + C) + F D := F.map_add _ _
    _ = (F (A + B) + F C) + F D :=
      congrArg (fun x => x + F D) (F.map_add (A + B) C)
    _ = ((F A + F B) + F C) + F D :=
      congrArg (fun x => (x + F C) + F D) (F.map_add A B)
    _ = 0 := by rw [hA, hB, hC, hD]; simp

section BlockSelectors

variable {K : Type u} [Field K] (q : ℕ)

/-! Extend an arbitrary routing table on the ambient coordinate basis to a
linear map out of one grading class. -/
noncomputable def blockBasisMap
    {U : TensorObj K 3} (sigma : Fin 3 → Fin 3)
    (out : ∀ s : Fin 3, Coord q s → U.V s) (s : Fin 3) :
    (grading K q).classOf s (sigma s) →ₗ[K] U.V s :=
  ((coordBasis K q s).constr K (out s)).comp
    ((grading K q).decomp s (sigma s)).subtype

private lemma blockBasisMap_apply_blockProj_basis
    {U : TensorObj K 3} (sigma : Fin 3 → Fin 3)
    (out : ∀ s : Fin 3, Coord q s → U.V s)
    (s : Fin 3) (i : Coord q s) :
    blockBasisMap q sigma out s
        ((grading K q).blockProj s (sigma s) (coordBasis K q s i)) =
      if coordGrade q s i = sigma s then out s i else 0 := by
  rw [blockProj_basis]
  split_ifs with h
  · change ((coordBasis K q s).constr K (out s))
        (coordBasis K q s i) = out s i
    exact Module.Basis.constr_basis (coordBasis K q s) K (out s) i
  · simp [blockBasisMap]

private lemma map_projected_basis_tprod
    {U : TensorObj K 3} (sigma : Fin 3 → Fin 3)
    (out : ∀ s : Fin 3, Coord q s → U.V s)
    (idx : ∀ s : Fin 3, Coord q s) :
    PiTensorProduct.map (blockBasisMap q sigma out)
        (PiTensorProduct.map
          (fun s => (grading K q).blockProj s (sigma s))
          (tprod K (fun s => coordBasis K q s (idx s)))) =
      tprod K (fun s =>
        if coordGrade q s (idx s) = sigma s then out s (idx s) else 0) := by
  have hin :
      PiTensorProduct.map (fun s => (grading K q).blockProj s (sigma s))
          (tprod K (fun s => coordBasis K q s (idx s))) =
        tprod K (fun s => (grading K q).blockProj s (sigma s)
          (coordBasis K q s (idx s))) :=
    PiTensorProduct.map_tprod _ _
  rw [hin, PiTensorProduct.map_tprod]
  congr 1
  funext s
  exact blockBasisMap_apply_blockProj_basis q sigma out s (idx s)

noncomputable def combinedMap
    {U : TensorObj K 3} (sigma : Fin 3 → Fin 3)
    (out : ∀ s : Fin 3, Coord q s → U.V s) :
    PiTensorProduct K (CoupledSpace K q) →ₗ[K] PiTensorProduct K U.V :=
  (PiTensorProduct.map (blockBasisMap q sigma out)).comp
    (PiTensorProduct.map
      (fun s => (grading K q).blockProj s (sigma s)))

private lemma combinedMap_basis_tprod_eq_of_grade_eq
    {U : TensorObj K 3} (sigma : Fin 3 → Fin 3)
    (out : ∀ s : Fin 3, Coord q s → U.V s)
    (idx : ∀ s : Fin 3, Coord q s)
    (hgrade : (fun s => coordGrade q s (idx s)) = sigma) :
    combinedMap q sigma out
        (tprod K (fun s => coordBasis K q s (idx s))) =
      tprod K (fun s => out s (idx s)) := by
  change PiTensorProduct.map (blockBasisMap q sigma out)
      (PiTensorProduct.map
        (fun s => (grading K q).blockProj s (sigma s))
        (tprod K (fun s => coordBasis K q s (idx s)))) = _
  rw [map_projected_basis_tprod]
  congr 1
  funext s
  simp [congrFun hgrade s]

private lemma combinedMap_basis_tprod_zero_of_grade_ne
    {U : TensorObj K 3} (sigma : Fin 3 → Fin 3)
    (out : ∀ s : Fin 3, Coord q s → U.V s)
    (idx : ∀ s : Fin 3, Coord q s)
    (hgrade : (fun s => coordGrade q s (idx s)) ≠ sigma) :
    combinedMap q sigma out
        (tprod K (fun s => coordBasis K q s (idx s))) = 0 := by
  change PiTensorProduct.map (blockBasisMap q sigma out)
      (PiTensorProduct.map
        (fun s => (grading K q).blockProj s (sigma s))
        (tprod K (fun s => coordBasis K q s (idx s)))) = 0
  rw [map_basis_tprod_zero_of_grade_ne K q sigma idx hgrade]
  exact LinearMap.map_zero _

private theorem combinedMap_coupledTensor_four_sums
    {U : TensorObj K 3} (sigma : Fin 3 → Fin 3)
    (out : ∀ s : Fin 3, Coord q s → U.V s) :
    combinedMap q sigma out (coupledTensor K q) =
      (((∑ i : Fin q, combinedMap q sigma out
          (tprod K (fun s => coordBasis K q s (term000 q i s)))) +
        (∑ k : Fin q, combinedMap q sigma out
          (tprod K (fun s => coordBasis K q s (term111 q k s))))) +
       (∑ i : Fin q, ∑ k : Fin q, combinedMap q sigma out
          (tprod K (fun s => coordBasis K q s (term012 q i k s))))) +
      (∑ i : Fin q, ∑ k : Fin q, combinedMap q sigma out
        (tprod K (fun s => coordBasis K q s (term102 q i k s)))) := by
  rw [coupledTensor_as_four_basis_sums]
  let F := combinedMap q sigma out
  let A := ∑ i : Fin q,
    tprod K (fun s => coordBasis K q s (term000 q i s))
  let B := ∑ k : Fin q,
    tprod K (fun s => coordBasis K q s (term111 q k s))
  let C := ∑ i : Fin q, ∑ k : Fin q,
    tprod K (fun s => coordBasis K q s (term012 q i k s))
  let D := ∑ i : Fin q, ∑ k : Fin q,
    tprod K (fun s => coordBasis K q s (term102 q i k s))
  change F (((A + B) + C) + D) = _
  calc
    F (((A + B) + C) + D) = F ((A + B) + C) + F D := F.map_add _ _
    _ = (F (A + B) + F C) + F D :=
      congrArg (fun x => x + F D) (F.map_add (A + B) C)
    _ = ((F A + F B) + F C) + F D :=
      congrArg (fun x => (x + F C) + F D) (F.map_add A B)
    _ = _ := by
      dsimp only [A, B, C, D]
      congr 1
      · congr 1
        · congr 1
          · exact map_sum F _ Finset.univ
          · exact map_sum F _ Finset.univ
        · calc
            F (∑ i : Fin q, ∑ k : Fin q,
                tprod K (fun s => coordBasis K q s (term012 q i k s))) =
                ∑ i : Fin q, F (∑ k : Fin q,
                  tprod K (fun s => coordBasis K q s (term012 q i k s))) :=
              map_sum F _ Finset.univ
            _ = _ := by
              apply Finset.sum_congr rfl
              intro i hi
              exact map_sum F _ Finset.univ
      · calc
          F (∑ i : Fin q, ∑ k : Fin q,
              tprod K (fun s => coordBasis K q s (term102 q i k s))) =
              ∑ i : Fin q, F (∑ k : Fin q,
                tprod K (fun s => coordBasis K q s (term102 q i k s))) :=
            map_sum F _ Finset.univ
          _ = _ := by
            apply Finset.sum_congr rfl
            intro i hi
            exact map_sum F _ Finset.univ

/-! The two diagonal grades use the same coordinate router; the grading
projection selects which copy survives. -/
noncomputable def lowOut :
    ∀ s : Fin 3, Coord q s → (MMObj K 1 q 1).V s
  | ⟨0, _⟩, Sum.inl i =>
      (Pi.single ((0 : Fin 1), i) 1 : Fin 1 × Fin q → K)
  | ⟨0, _⟩, Sum.inr i =>
      (Pi.single ((0 : Fin 1), i) 1 : Fin 1 × Fin q → K)
  | ⟨1, _⟩, Sum.inl i =>
      (Pi.single (i, (0 : Fin 1)) 1 : Fin q × Fin 1 → K)
  | ⟨1, _⟩, Sum.inr i =>
      (Pi.single (i, (0 : Fin 1)) 1 : Fin q × Fin 1 → K)
  | ⟨2, _⟩, _ =>
      (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1 : Fin 1 × Fin 1 → K)

/-! Likewise one router realizes both crossed grades. -/
noncomputable def highOut :
    ∀ s : Fin 3, Coord q s → (MMObj K q 1 q).V s
  | ⟨0, _⟩, Sum.inl i =>
      (Pi.single (i, (0 : Fin 1)) 1 : Fin q × Fin 1 → K)
  | ⟨0, _⟩, Sum.inr i =>
      (Pi.single (i, (0 : Fin 1)) 1 : Fin q × Fin 1 → K)
  | ⟨1, _⟩, Sum.inl k =>
      (Pi.single ((0 : Fin 1), k) 1 : Fin 1 × Fin q → K)
  | ⟨1, _⟩, Sum.inr k =>
      (Pi.single ((0 : Fin 1), k) 1 : Fin 1 × Fin q → K)
  | ⟨2, _⟩, Sum.inl _ => 0
  | ⟨2, _⟩, Sum.inr (i, k) =>
      (Pi.single (k, i) 1 : Fin q × Fin q → K)

/-! The other crossed block exchanges the roles of its two source indices
in mode two. -/
noncomputable def highOut102 :
    ∀ s : Fin 3, Coord q s → (MMObj K q 1 q).V s
  | ⟨0, _⟩, Sum.inl i =>
      (Pi.single (i, (0 : Fin 1)) 1 : Fin q × Fin 1 → K)
  | ⟨0, _⟩, Sum.inr i =>
      (Pi.single (i, (0 : Fin 1)) 1 : Fin q × Fin 1 → K)
  | ⟨1, _⟩, Sum.inl k =>
      (Pi.single ((0 : Fin 1), k) 1 : Fin 1 × Fin q → K)
  | ⟨1, _⟩, Sum.inr k =>
      (Pi.single ((0 : Fin 1), k) 1 : Fin 1 × Fin q → K)
  | ⟨2, _⟩, Sum.inl _ => 0
  | ⟨2, _⟩, Sum.inr (i, k) =>
      (Pi.single (i, k) 1 : Fin q × Fin q → K)

theorem low000_restrict :
    TensorObj.Restrict (MMObj K 1 q 1)
      ((grading K q).blockSubtensor ![0, 0, 0]) := by
  refine ⟨blockBasisMap q ![0, 0, 0] (lowOut q), ?_⟩
  change PiTensorProduct.map
      (blockBasisMap q ![0, 0, 0] (lowOut q))
      ((grading K q).blockTensor ![0, 0, 0]) = MMTensor K 1 q 1
  change combinedMap q ![0, 0, 0] (lowOut q) (coupledTensor K q) =
    MMTensor K 1 q 1
  rw [combinedMap_coupledTensor_four_sums]
  have hm (i : Fin q) :
      combinedMap q ![0, 0, 0] (lowOut q)
          (tprod K (fun s => coordBasis K q s (term000 q i s))) =
        tprod K (fun s => lowOut q s (term000 q i s)) := by
    apply combinedMap_basis_tprod_eq_of_grade_eq
    rw [term000_grade]
    funext s
    fin_cases s <;> rfl
  have hz111 (k : Fin q) :
      combinedMap q ![0, 0, 0] (lowOut q)
          (tprod K (fun s => coordBasis K q s (term111 q k s))) = 0 := by
    apply combinedMap_basis_tprod_zero_of_grade_ne
    rw [term111_grade]
    decide
  have hz012 (i k : Fin q) :
      combinedMap q ![0, 0, 0] (lowOut q)
          (tprod K (fun s => coordBasis K q s (term012 q i k s))) = 0 := by
    apply combinedMap_basis_tprod_zero_of_grade_ne
    rw [term012_grade]
    decide
  have hz102 (i k : Fin q) :
      combinedMap q ![0, 0, 0] (lowOut q)
          (tprod K (fun s => coordBasis K q s (term102 q i k s))) = 0 := by
    apply combinedMap_basis_tprod_zero_of_grade_ne
    rw [term102_grade]
    decide
  simp_rw [hm, hz111, hz012, hz102]
  simp only [Finset.sum_const_zero, add_zero]
  unfold MMTensor
  simp only [Fin.sum_univ_one]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  funext s
  fin_cases s <;> rfl

theorem low111_restrict :
    TensorObj.Restrict (MMObj K 1 q 1)
      ((grading K q).blockSubtensor ![1, 1, 1]) := by
  refine ⟨blockBasisMap q ![1, 1, 1] (lowOut q), ?_⟩
  change PiTensorProduct.map
      (blockBasisMap q ![1, 1, 1] (lowOut q))
      ((grading K q).blockTensor ![1, 1, 1]) = MMTensor K 1 q 1
  change combinedMap q ![1, 1, 1] (lowOut q) (coupledTensor K q) =
    MMTensor K 1 q 1
  rw [combinedMap_coupledTensor_four_sums]
  have hz000 (i : Fin q) :
      combinedMap q ![1, 1, 1] (lowOut q)
          (tprod K (fun s => coordBasis K q s (term000 q i s))) = 0 := by
    apply combinedMap_basis_tprod_zero_of_grade_ne
    rw [term000_grade]
    decide
  have hm (k : Fin q) :
      combinedMap q ![1, 1, 1] (lowOut q)
          (tprod K (fun s => coordBasis K q s (term111 q k s))) =
        tprod K (fun s => lowOut q s (term111 q k s)) := by
    apply combinedMap_basis_tprod_eq_of_grade_eq
    rw [term111_grade]
    funext s
    fin_cases s <;> rfl
  have hz012 (i k : Fin q) :
      combinedMap q ![1, 1, 1] (lowOut q)
          (tprod K (fun s => coordBasis K q s (term012 q i k s))) = 0 := by
    apply combinedMap_basis_tprod_zero_of_grade_ne
    rw [term012_grade]
    decide
  have hz102 (i k : Fin q) :
      combinedMap q ![1, 1, 1] (lowOut q)
          (tprod K (fun s => coordBasis K q s (term102 q i k s))) = 0 := by
    apply combinedMap_basis_tprod_zero_of_grade_ne
    rw [term102_grade]
    decide
  simp_rw [hz000, hm, hz012, hz102]
  simp only [Finset.sum_const_zero, zero_add, add_zero]
  unfold MMTensor
  simp only [Fin.sum_univ_one]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  funext s
  fin_cases s <;> rfl

theorem high012_restrict :
    TensorObj.Restrict (MMObj K q 1 q)
      ((grading K q).blockSubtensor ![0, 1, 2]) := by
  refine ⟨blockBasisMap q ![0, 1, 2] (highOut q), ?_⟩
  change PiTensorProduct.map
      (blockBasisMap q ![0, 1, 2] (highOut q))
      ((grading K q).blockTensor ![0, 1, 2]) = MMTensor K q 1 q
  change combinedMap q ![0, 1, 2] (highOut q) (coupledTensor K q) =
    MMTensor K q 1 q
  rw [combinedMap_coupledTensor_four_sums]
  have hz000 (i : Fin q) :
      combinedMap q ![0, 1, 2] (highOut q)
          (tprod K (fun s => coordBasis K q s (term000 q i s))) = 0 := by
    apply combinedMap_basis_tprod_zero_of_grade_ne
    rw [term000_grade]
    decide
  have hz111 (k : Fin q) :
      combinedMap q ![0, 1, 2] (highOut q)
          (tprod K (fun s => coordBasis K q s (term111 q k s))) = 0 := by
    apply combinedMap_basis_tprod_zero_of_grade_ne
    rw [term111_grade]
    decide
  have hm (i k : Fin q) :
      combinedMap q ![0, 1, 2] (highOut q)
          (tprod K (fun s => coordBasis K q s (term012 q i k s))) =
        tprod K (fun s => highOut q s (term012 q i k s)) := by
    apply combinedMap_basis_tprod_eq_of_grade_eq
    rw [term012_grade]
    funext s
    fin_cases s <;> rfl
  have hz102 (i k : Fin q) :
      combinedMap q ![0, 1, 2] (highOut q)
          (tprod K (fun s => coordBasis K q s (term102 q i k s))) = 0 := by
    apply combinedMap_basis_tprod_zero_of_grade_ne
    rw [term102_grade]
    decide
  simp_rw [hz000, hz111, hm, hz102]
  simp only [Finset.sum_const_zero, zero_add, add_zero]
  unfold MMTensor
  simp only [Fin.sum_univ_one]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  funext s
  fin_cases s <;> rfl

theorem high102_restrict :
    TensorObj.Restrict (MMObj K q 1 q)
      ((grading K q).blockSubtensor ![1, 0, 2]) := by
  refine ⟨blockBasisMap q ![1, 0, 2] (highOut102 q), ?_⟩
  change PiTensorProduct.map
      (blockBasisMap q ![1, 0, 2] (highOut102 q))
      ((grading K q).blockTensor ![1, 0, 2]) = MMTensor K q 1 q
  change combinedMap q ![1, 0, 2] (highOut102 q) (coupledTensor K q) =
    MMTensor K q 1 q
  rw [combinedMap_coupledTensor_four_sums]
  have hz000 (i : Fin q) :
      combinedMap q ![1, 0, 2] (highOut102 q)
          (tprod K (fun s => coordBasis K q s (term000 q i s))) = 0 := by
    apply combinedMap_basis_tprod_zero_of_grade_ne
    rw [term000_grade]
    decide
  have hz111 (k : Fin q) :
      combinedMap q ![1, 0, 2] (highOut102 q)
          (tprod K (fun s => coordBasis K q s (term111 q k s))) = 0 := by
    apply combinedMap_basis_tprod_zero_of_grade_ne
    rw [term111_grade]
    decide
  have hz012 (i k : Fin q) :
      combinedMap q ![1, 0, 2] (highOut102 q)
          (tprod K (fun s => coordBasis K q s (term012 q i k s))) = 0 := by
    apply combinedMap_basis_tprod_zero_of_grade_ne
    rw [term012_grade]
    decide
  have hm (i k : Fin q) :
      combinedMap q ![1, 0, 2] (highOut102 q)
          (tprod K (fun s => coordBasis K q s (term102 q i k s))) =
        tprod K (fun s => highOut102 q s (term102 q i k s)) := by
    apply combinedMap_basis_tprod_eq_of_grade_eq
    rw [term102_grade]
    funext s
    fin_cases s <;> rfl
  simp_rw [hz000, hz111, hz012, hm]
  simp only [Finset.sum_const_zero, zero_add]
  unfold MMTensor
  simp only [Fin.sum_univ_one]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  funext s
  fin_cases s <;> rfl

end BlockSelectors

end CoupledThreeGrading

theorem solution
    {K : Type u} [Field K] (q : ℕ) :
    ∃ grading : (coupledObj K q).TypeGrading 3,
      (∀ sigma : Fin 3 → Fin 3,
        sigma ≠ ![0, 0, 0] → sigma ≠ ![1, 1, 1] →
        sigma ≠ ![0, 1, 2] → sigma ≠ ![1, 0, 2] →
        grading.blockTensor sigma = 0) ∧
      TensorObj.Restrict (MMObj K 1 q 1)
        (grading.blockSubtensor ![0, 0, 0]) ∧
      TensorObj.Restrict (MMObj K 1 q 1)
        (grading.blockSubtensor ![1, 1, 1]) ∧
      TensorObj.Restrict (MMObj K q 1 q)
        (grading.blockSubtensor ![0, 1, 2]) ∧
      TensorObj.Restrict (MMObj K q 1 q)
        (grading.blockSubtensor ![1, 0, 2]) := by
  refine ⟨CoupledThreeGrading.grading K q, ?_,
    CoupledThreeGrading.low000_restrict q,
    CoupledThreeGrading.low111_restrict q,
    CoupledThreeGrading.high012_restrict q,
    CoupledThreeGrading.high102_restrict q⟩
  intro sigma h000 h111 h012 h102
  exact CoupledThreeGrading.support K q sigma h000 h111 h012 h102
