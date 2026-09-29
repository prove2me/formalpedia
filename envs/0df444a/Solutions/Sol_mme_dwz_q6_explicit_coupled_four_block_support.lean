-- Prove2me | solution 1 for mme_dwz_q6_explicit_coupled_four_block_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T08:16:24.931366+00:00
-- url     : https://prove2.me/submissions/1a5746b1-a4fb-451a-99ad-4b3406b2d855

import Definitions.Def_mme_CW_square_canonical_grading
import Definitions.Def_mme_dwz_q6_coupled_explicit_grading
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_block_subtensor
import Definitions.Def_mme_tensor_quotient
import Mathlib.Tactic

open MME PiTensorProduct BigOperators DirectSum Module

universe u

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace DWZQ6SupportProof

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

instance coordFinite (q : ℕ) (s : Fin 3) : Finite (Coord q s) :=
  match s with
  | ⟨0, _⟩ => inferInstanceAs (Finite (Fin q ⊕ Fin q))
  | ⟨1, _⟩ => inferInstanceAs (Finite (Fin q ⊕ Fin q))
  | ⟨2, _⟩ => inferInstanceAs (Finite (Fin 2 ⊕ (Fin q × Fin q)))

instance coordDecidableEq (q : ℕ) (s : Fin 3) :
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

lemma basis_mem_grade
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) (a : Coord q s) :
    coordBasis K q s a ∈
      (grading K q).decomp s (coordGrade q s a) := by
  exact Submodule.subset_span ⟨a, rfl, rfl⟩

lemma blockProj_apply_mem
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

lemma blockProj_apply_mem_ne
    {K : Type u} [Field K] {d t : ℕ} {T : TensorObj K d}
    (G : T.TypeGrading t) (s : Fin d) (a b : Fin t) (hab : a ≠ b)
    (x : T.V s) (hx : x ∈ G.decomp s b) :
    G.blockProj s a x = 0 := by
  unfold TensorObj.TypeGrading.blockProj TensorObj.TypeGrading.modeLequiv
  simp only [LinearMap.comp_apply]
  rw [← DirectSum.apply_eq_component]
  exact (G.is_internal s).ofBijective_coeLinearMap_of_mem_ne hab.symm hx

lemma blockProj_basis
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

lemma coordBasis_apply_zero
    (K : Type u) [Field K] (q : ℕ) (i : Fin q ⊕ Fin q) :
    coordBasis K q (0 : Fin 3) i = Pi.single i 1 := by
  classical
  change (Pi.basisFun K (Fin q ⊕ Fin q)) i = Pi.single i 1
  exact Pi.basisFun_apply K _ i

lemma coordBasis_apply_one
    (K : Type u) [Field K] (q : ℕ) (i : Fin q ⊕ Fin q) :
    coordBasis K q (1 : Fin 3) i = Pi.single i 1 := by
  classical
  change (Pi.basisFun K (Fin q ⊕ Fin q)) i = Pi.single i 1
  exact Pi.basisFun_apply K _ i

lemma coordBasis_apply_two
    (K : Type u) [Field K] (q : ℕ) (i : Fin 2 ⊕ (Fin q × Fin q)) :
    coordBasis K q (2 : Fin 3) i = Pi.single i 1 := by
  classical
  change (Pi.basisFun K (Fin 2 ⊕ (Fin q × Fin q))) i = Pi.single i 1
  exact Pi.basisFun_apply K _ i

def blockType (a b c : Fin 3) : Fin 3 → Fin 3
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c

def term000 (q : ℕ) (i : Fin q) : ∀ s : Fin 3, Coord q s
  | ⟨0, _⟩ => Sum.inl i
  | ⟨1, _⟩ => Sum.inl i
  | ⟨2, _⟩ => Sum.inl 0

def term111 (q : ℕ) (k : Fin q) : ∀ s : Fin 3, Coord q s
  | ⟨0, _⟩ => Sum.inr k
  | ⟨1, _⟩ => Sum.inr k
  | ⟨2, _⟩ => Sum.inl 1

def term012 (q : ℕ) (i k : Fin q) : ∀ s : Fin 3, Coord q s
  | ⟨0, _⟩ => Sum.inl i
  | ⟨1, _⟩ => Sum.inr k
  | ⟨2, _⟩ => Sum.inr (i, k)

def term102 (q : ℕ) (i k : Fin q) : ∀ s : Fin 3, Coord q s
  | ⟨0, _⟩ => Sum.inr k
  | ⟨1, _⟩ => Sum.inl i
  | ⟨2, _⟩ => Sum.inr (i, k)

noncomputable def raw000
    (K : Type u) [Field K] (q : ℕ) (i : Fin q) :
    PiTensorProduct K (CoupledSpace K q) :=
  tprod K (fun s =>
    match s with
    | ⟨0, _⟩ => (Pi.single (Sum.inl i) 1 : (Fin q ⊕ Fin q) → K)
    | ⟨1, _⟩ => (Pi.single (Sum.inl i) 1 : (Fin q ⊕ Fin q) → K)
    | ⟨2, _⟩ => (Pi.single (Sum.inl (0 : Fin 2)) 1 :
        (Fin 2 ⊕ (Fin q × Fin q)) → K))

noncomputable def raw111
    (K : Type u) [Field K] (q : ℕ) (k : Fin q) :
    PiTensorProduct K (CoupledSpace K q) :=
  tprod K (fun s =>
    match s with
    | ⟨0, _⟩ => (Pi.single (Sum.inr k) 1 : (Fin q ⊕ Fin q) → K)
    | ⟨1, _⟩ => (Pi.single (Sum.inr k) 1 : (Fin q ⊕ Fin q) → K)
    | ⟨2, _⟩ => (Pi.single (Sum.inl (1 : Fin 2)) 1 :
        (Fin 2 ⊕ (Fin q × Fin q)) → K))

noncomputable def raw012
    (K : Type u) [Field K] (q : ℕ) (i k : Fin q) :
    PiTensorProduct K (CoupledSpace K q) :=
  tprod K (fun s =>
    match s with
    | ⟨0, _⟩ => (Pi.single (Sum.inl i) 1 : (Fin q ⊕ Fin q) → K)
    | ⟨1, _⟩ => (Pi.single (Sum.inr k) 1 : (Fin q ⊕ Fin q) → K)
    | ⟨2, _⟩ => (Pi.single (Sum.inr (i, k)) 1 :
        (Fin 2 ⊕ (Fin q × Fin q)) → K))

noncomputable def raw102
    (K : Type u) [Field K] (q : ℕ) (i k : Fin q) :
    PiTensorProduct K (CoupledSpace K q) :=
  tprod K (fun s =>
    match s with
    | ⟨0, _⟩ => (Pi.single (Sum.inr k) 1 : (Fin q ⊕ Fin q) → K)
    | ⟨1, _⟩ => (Pi.single (Sum.inl i) 1 : (Fin q ⊕ Fin q) → K)
    | ⟨2, _⟩ => (Pi.single (Sum.inr (i, k)) 1 :
        (Fin 2 ⊕ (Fin q × Fin q)) → K))

lemma term000_grade (q : ℕ) (i : Fin q) :
    (fun s => coordGrade q s (term000 q i s)) = blockType 0 0 0 := by
  funext s
  fin_cases s <;> rfl

lemma term111_grade (q : ℕ) (k : Fin q) :
    (fun s => coordGrade q s (term111 q k s)) = blockType 1 1 1 := by
  funext s
  fin_cases s <;> rfl

lemma term012_grade (q : ℕ) (i k : Fin q) :
    (fun s => coordGrade q s (term012 q i k s)) = blockType 0 1 2 := by
  funext s
  fin_cases s <;> rfl

lemma term102_grade (q : ℕ) (i k : Fin q) :
    (fun s => coordGrade q s (term102 q i k s)) = blockType 1 0 2 := by
  funext s
  fin_cases s <;> rfl

lemma map_basis_tprod_zero_of_grade_ne
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
  apply MultilinearMap.map_coord_zero (PiTensorProduct.tprod K) s
  exact blockProj_apply_mem_ne (grading K q) s (sigma s)
    (coordGrade q s (idx s)) hs.symm _ (basis_mem_grade K q s (idx s))

lemma coupledTensor_as_four_basis_sums
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


end DWZQ6SupportProof

open MME.DWZComponentRestriction

theorem solution
    {K : Type u} [Field K]
    (σ : Fin 3 → Fin 3)
    (h000 : σ ≠ ![0, 0, 0])
    (h111 : σ ≠ ![1, 1, 1])
    (h012 : σ ≠ ![0, 1, 2])
    (h102 : σ ≠ ![1, 0, 2]) :
    (dwzQ6CoupledGrading K).blockTensor σ = 0 := by
  have hgrade :
      dwzQ6CoupledGrading K = DWZQ6SupportProof.grading K 6 := by
    unfold dwzQ6CoupledGrading DWZQ6SupportProof.grading
    congr 1
    funext s a
    fin_cases s <;>
      change cwBasisGrade (Pi.basisFun K _) _ a =
        cwBasisGrade (Pi.basisFun K _) _ a <;>
      congr 1 <;>
      funext c <;>
      rcases c with c | c <;> rfl
  rw [hgrade]
  exact DWZQ6SupportProof.support K 6 σ h000 h111 h012 h102
