-- Prove2me | solution 1 for mme_CW_block_is_MM_at_110
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-06-05T03:26:26.811286+00:00
-- url     : https://prove2.me/submissions/a942689a-0f62-45d9-b1d2-7a611991affe

import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Definitions.Def_mme_block_subtensor
import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_CW_canonical_grading
import Definitions.Def_mme_tensor_rank
import Definitions.Def_mme_tensor_type_grading
import Definitions.Def_mme_omega

open MME



/-! # `Sol_mme_CW_block_is_MM_at_110` — closes `mme_CW_block_is_MM_at_110`.

For the canonical 3-grading, the σ-block at σ=(1,1,0) extracts
`∑ⱼ e_{Mⱼ} ⊗ e_{Mⱼ} ⊗ e_O` from `T_q`, which after class-isomorphism is
`MMObj K 1 q 1` = `∑ⱼ tprod (single (0,j) 1, single (j,0) 1, single (0,0) 1)`.

Status: LOCAL ONLY. -/

set_option maxHeartbeats 1200000

open MME PiTensorProduct BigOperators

universe u

namespace MMECWBlockAt110Sol

variable {K : Type u} [Field K] {q : ℕ}

def σ_110 : Fin 3 → Fin 3 := fun i =>
  match i with
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 0

noncomputable def toMM (K : Type u) [Field K] (q : ℕ) :
    ∀ i : Fin 3,
      ((cwCanonicalGrading q (K := K)).blockSubtensor σ_110).V i →ₗ[K]
        (MMObj K 1 q 1).V i :=
  fun i =>
    match i with
    | ⟨0, _⟩ =>
      ∑ j : Fin q,
        LinearMap.smulRight
          ((LinearMap.proj (⟨j.val+1, by omega⟩ : Fin (q+2)) :
              (Fin (q+2) → K) →ₗ[K] K).comp
            (Submodule.subtype (cwGradePiece K q 1)))
          (Pi.single (0, j) 1 : Fin 1 × Fin q → K)
    | ⟨1, _⟩ =>
      ∑ j : Fin q,
        LinearMap.smulRight
          ((LinearMap.proj (⟨j.val+1, by omega⟩ : Fin (q+2)) :
              (Fin (q+2) → K) →ₗ[K] K).comp
            (Submodule.subtype (cwGradePiece K q 1)))
          (Pi.single (j, 0) 1 : Fin q × Fin 1 → K)
    | ⟨2, _⟩ =>
      LinearMap.smulRight
        ((LinearMap.proj (⟨0, by omega⟩ : Fin (q+2)) :
            (Fin (q+2) → K) →ₗ[K] K).comp
          (Submodule.subtype (cwGradePiece K q 0)))
        (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)

/-! ## blockProj evaluation helpers. -/

private lemma blockProj_eq_aux {d t : ℕ} {T : TensorObj K d}
    (G : T.TypeGrading t) (i : Fin d) (α : Fin t) (x : T.V i) :
    G.blockProj i α x =
      DirectSum.component K (Fin t)
        (fun β => (G.classOf i β : Submodule K (T.V i))) α
        ((G.modeLequiv i).symm x) := rfl

private lemma modeLequiv_symm_apply_aux {d t : ℕ} {T : TensorObj K d}
    (G : T.TypeGrading t) (i : Fin d) (x : T.V i) :
    (G.modeLequiv i).symm x =
      (LinearEquiv.ofBijective
        (DirectSum.coeLinearMap fun α => (G.classOf i α : Submodule K (T.V i)))
        (G.is_internal i)).symm x := rfl

private lemma subtype_blockProj_self {d t : ℕ} {T : TensorObj K d}
    (G : T.TypeGrading t)
    (i : Fin d) (α : Fin t) (v : T.V i) (hv : v ∈ G.classOf i α) :
    (G.classOf i α).subtype (G.blockProj i α v) = v := by
  rw [blockProj_eq_aux, modeLequiv_symm_apply_aux]
  show ((((LinearEquiv.ofBijective
        (DirectSum.coeLinearMap fun β => (G.classOf i β : Submodule K (T.V i)))
        (G.is_internal i)).symm v) α : G.classOf i α) : T.V i) = v
  rw [DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem (G.is_internal i) hv]

private lemma subtype_blockProj_ne {d t : ℕ} {T : TensorObj K d}
    (G : T.TypeGrading t)
    (i : Fin d) {α α' : Fin t} (hαα' : α ≠ α') (v : T.V i) (hv : v ∈ G.classOf i α) :
    (G.classOf i α').subtype (G.blockProj i α' v) = 0 := by
  rw [blockProj_eq_aux, modeLequiv_symm_apply_aux]
  show ((((LinearEquiv.ofBijective
        (DirectSum.coeLinearMap fun β => (G.classOf i β : Submodule K (T.V i)))
        (G.is_internal i)).symm v) α' : G.classOf i α') : T.V i) = 0
  rw [DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem_ne (G.is_internal i) hαα' hv]
  rfl

private lemma cw_subtype_blockProj_self_0 (q : ℕ) (α : Fin 3)
    (v : Fin (q+2) → K) (hv : v ∈ cwGradePiece K q α) :
    (cwGradePiece K q α).subtype
      ((cwCanonicalGrading q (K := K)).blockProj ⟨0, by omega⟩ α v) = v :=
  subtype_blockProj_self (cwCanonicalGrading q) ⟨0, by omega⟩ α v hv

private lemma cw_subtype_blockProj_self_1 (q : ℕ) (α : Fin 3)
    (v : Fin (q+2) → K) (hv : v ∈ cwGradePiece K q α) :
    (cwGradePiece K q α).subtype
      ((cwCanonicalGrading q (K := K)).blockProj ⟨1, by omega⟩ α v) = v :=
  subtype_blockProj_self (cwCanonicalGrading q) ⟨1, by omega⟩ α v hv

private lemma cw_subtype_blockProj_self_2 (q : ℕ) (α : Fin 3)
    (v : Fin (q+2) → K) (hv : v ∈ cwGradePiece K q α) :
    (cwGradePiece K q α).subtype
      ((cwCanonicalGrading q (K := K)).blockProj ⟨2, by omega⟩ α v) = v :=
  subtype_blockProj_self (cwCanonicalGrading q) ⟨2, by omega⟩ α v hv

private lemma cw_subtype_blockProj_ne_0 (q : ℕ) {α α' : Fin 3}
    (hαα' : α ≠ α') (v : Fin (q+2) → K) (hv : v ∈ cwGradePiece K q α) :
    (cwGradePiece K q α').subtype
      ((cwCanonicalGrading q (K := K)).blockProj ⟨0, by omega⟩ α' v) = 0 :=
  subtype_blockProj_ne (cwCanonicalGrading q) ⟨0, by omega⟩ hαα' v hv

private lemma cw_subtype_blockProj_ne_1 (q : ℕ) {α α' : Fin 3}
    (hαα' : α ≠ α') (v : Fin (q+2) → K) (hv : v ∈ cwGradePiece K q α) :
    (cwGradePiece K q α').subtype
      ((cwCanonicalGrading q (K := K)).blockProj ⟨1, by omega⟩ α' v) = 0 :=
  subtype_blockProj_ne (cwCanonicalGrading q) ⟨1, by omega⟩ hαα' v hv

private lemma cw_subtype_blockProj_ne_2 (q : ℕ) {α α' : Fin 3}
    (hαα' : α ≠ α') (v : Fin (q+2) → K) (hv : v ∈ cwGradePiece K q α) :
    (cwGradePiece K q α').subtype
      ((cwCanonicalGrading q (K := K)).blockProj ⟨2, by omega⟩ α' v) = 0 :=
  subtype_blockProj_ne (cwCanonicalGrading q) ⟨2, by omega⟩ hαα' v hv

/-! ## Pointwise apply lemmas. -/

private lemma toMM0_apply (K : Type u) [Field K] (q : ℕ)
    (w : cwGradePiece K q 1) :
    toMM K q ⟨0, by omega⟩ w =
      ∑ j : Fin q, ((cwGradePiece K q 1).subtype w ⟨j.val+1, by omega⟩) •
        (Pi.single (0, j) 1 : Fin 1 × Fin q → K) := by
  show (∑ j : Fin q,
        LinearMap.smulRight
          ((LinearMap.proj (⟨j.val+1, by omega⟩ : Fin (q+2)) :
              (Fin (q+2) → K) →ₗ[K] K).comp
            (Submodule.subtype (cwGradePiece K q 1)))
          (Pi.single (0, j) 1 : Fin 1 × Fin q → K)) w = _
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intros j _
  rw [LinearMap.smulRight_apply, LinearMap.comp_apply, LinearMap.proj_apply]

private lemma toMM1_apply (K : Type u) [Field K] (q : ℕ)
    (w : cwGradePiece K q 1) :
    toMM K q ⟨1, by omega⟩ w =
      ∑ j : Fin q, ((cwGradePiece K q 1).subtype w ⟨j.val+1, by omega⟩) •
        (Pi.single (j, 0) 1 : Fin q × Fin 1 → K) := by
  show (∑ j : Fin q,
        LinearMap.smulRight
          ((LinearMap.proj (⟨j.val+1, by omega⟩ : Fin (q+2)) :
              (Fin (q+2) → K) →ₗ[K] K).comp
            (Submodule.subtype (cwGradePiece K q 1)))
          (Pi.single (j, 0) 1 : Fin q × Fin 1 → K)) w = _
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intros j _
  rw [LinearMap.smulRight_apply, LinearMap.comp_apply, LinearMap.proj_apply]

private lemma toMM2_apply (K : Type u) [Field K] (q : ℕ)
    (w : cwGradePiece K q 0) :
    toMM K q ⟨2, by omega⟩ w =
      ((cwGradePiece K q 0).subtype w ⟨0, by omega⟩) •
        (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) := by
  show LinearMap.smulRight ((LinearMap.proj (⟨0, by omega⟩ : Fin (q+2)) :
        (Fin (q+2) → K) →ₗ[K] K).comp
        (Submodule.subtype (cwGradePiece K q 0)))
      (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) w = _
  rw [LinearMap.smulRight_apply, LinearMap.comp_apply, LinearMap.proj_apply]

/-- σ_110 0 = 1, M-input. -/
private lemma toMM_blockProj_at0_M (K : Type u) [Field K] (q : ℕ) (i : Fin q) :
    (toMM K q ⟨0, by omega⟩)
      ((cwCanonicalGrading q (K := K)).blockProj ⟨0, by omega⟩ 1
        (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K)) =
      (Pi.single (0, i) 1 : Fin 1 × Fin q → K) := by
  classical
  refine (toMM0_apply K q _).trans ?_
  have hmem : (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K) ∈
      cwGradePiece K q 1 := by
    have h := single_mem_cwGradePiece (K := K) q (⟨i.val+1, by omega⟩ : Fin (q+2))
    have hi : i.val < q := i.isLt
    have htype : typeOfCW q (⟨i.val+1, by omega⟩ : Fin (q+2)) = 1 := by
      simp [typeOfCW]; omega
    rw [htype] at h; exact h
  rw [cw_subtype_blockProj_self_0 q 1
      (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K) hmem]
  rw [Finset.sum_eq_single i]
  · have : (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K)
        ⟨i.val+1, by omega⟩ = 1 := Pi.single_eq_same _ _
    rw [this]; rw [one_smul]
  · intros j _ hji
    have hi : i.val < q := i.isLt
    have hj : j.val < q := j.isLt
    have hne : (⟨j.val+1, by omega⟩ : Fin (q+2)) ≠ (⟨i.val+1, by omega⟩ : Fin (q+2)) := by
      intro heq
      apply hji
      have := congrArg Fin.val heq
      simp at this
      exact Fin.ext (by omega)
    rw [Pi.single_eq_of_ne hne 1]; rw [zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma toMM_blockProj_at0_O (K : Type u) [Field K] (q : ℕ) :
    (toMM K q ⟨0, by omega⟩)
      ((cwCanonicalGrading q (K := K)).blockProj ⟨0, by omega⟩ 1
        (Pi.single (⟨0, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K)) = 0 := by
  classical
  refine (toMM0_apply K q _).trans ?_
  have hmem : (Pi.single (⟨0, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K) ∈
      cwGradePiece K q 0 := by
    have h := single_mem_cwGradePiece (K := K) q (⟨0, by omega⟩ : Fin (q+2))
    rw [typeOfCW_zero] at h; exact h
  have hne : (0 : Fin 3) ≠ 1 := by decide
  rw [cw_subtype_blockProj_ne_0 q hne
      (Pi.single (⟨0, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K) hmem]
  apply Finset.sum_eq_zero
  intros j _
  show ((0 : Fin (q+2) → K) ⟨j.val+1, by omega⟩ : K) •
        (Pi.single (0, j) 1 : Fin 1 × Fin q → K) = 0
  rw [Pi.zero_apply, zero_smul]

private lemma toMM_blockProj_at0_T (K : Type u) [Field K] (q : ℕ) :
    (toMM K q ⟨0, by omega⟩)
      ((cwCanonicalGrading q (K := K)).blockProj ⟨0, by omega⟩ 1
        (Pi.single (⟨q+1, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K)) = 0 := by
  classical
  refine (toMM0_apply K q _).trans ?_
  have hmem : (Pi.single (⟨q+1, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K) ∈
      cwGradePiece K q 2 := by
    have h := single_mem_cwGradePiece (K := K) q (⟨q+1, by omega⟩ : Fin (q+2))
    rw [typeOfCW_qPlusOne] at h; exact h
  have hne : (2 : Fin 3) ≠ 1 := by decide
  rw [cw_subtype_blockProj_ne_0 q hne
      (Pi.single (⟨q+1, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K) hmem]
  apply Finset.sum_eq_zero
  intros j _
  show ((0 : Fin (q+2) → K) ⟨j.val+1, by omega⟩ : K) •
        (Pi.single (0, j) 1 : Fin 1 × Fin q → K) = 0
  rw [Pi.zero_apply, zero_smul]

/-- σ_110 1 = 1, M-input. -/
private lemma toMM_blockProj_at1_M (K : Type u) [Field K] (q : ℕ) (i : Fin q) :
    (toMM K q ⟨1, by omega⟩)
      ((cwCanonicalGrading q (K := K)).blockProj ⟨1, by omega⟩ 1
        (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K)) =
      (Pi.single (i, 0) 1 : Fin q × Fin 1 → K) := by
  classical
  refine (toMM1_apply K q _).trans ?_
  have hmem : (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K) ∈
      cwGradePiece K q 1 := by
    have h := single_mem_cwGradePiece (K := K) q (⟨i.val+1, by omega⟩ : Fin (q+2))
    have hi : i.val < q := i.isLt
    have htype : typeOfCW q (⟨i.val+1, by omega⟩ : Fin (q+2)) = 1 := by
      simp [typeOfCW]; omega
    rw [htype] at h; exact h
  rw [cw_subtype_blockProj_self_1 q 1
      (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K) hmem]
  rw [Finset.sum_eq_single i]
  · have : (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K)
        ⟨i.val+1, by omega⟩ = 1 := Pi.single_eq_same _ _
    rw [this]; rw [one_smul]
  · intros j _ hji
    have hi : i.val < q := i.isLt
    have hj : j.val < q := j.isLt
    have hne : (⟨j.val+1, by omega⟩ : Fin (q+2)) ≠ (⟨i.val+1, by omega⟩ : Fin (q+2)) := by
      intro heq
      apply hji
      have := congrArg Fin.val heq
      simp at this
      exact Fin.ext (by omega)
    rw [Pi.single_eq_of_ne hne 1]; rw [zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma toMM_blockProj_at1_O (K : Type u) [Field K] (q : ℕ) :
    (toMM K q ⟨1, by omega⟩)
      ((cwCanonicalGrading q (K := K)).blockProj ⟨1, by omega⟩ 1
        (Pi.single (⟨0, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K)) = 0 := by
  classical
  refine (toMM1_apply K q _).trans ?_
  have hmem : (Pi.single (⟨0, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K) ∈
      cwGradePiece K q 0 := by
    have h := single_mem_cwGradePiece (K := K) q (⟨0, by omega⟩ : Fin (q+2))
    rw [typeOfCW_zero] at h; exact h
  have hne : (0 : Fin 3) ≠ 1 := by decide
  rw [cw_subtype_blockProj_ne_1 q hne
      (Pi.single (⟨0, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K) hmem]
  apply Finset.sum_eq_zero
  intros j _
  show ((0 : Fin (q+2) → K) ⟨j.val+1, by omega⟩ : K) •
        (Pi.single (j, 0) 1 : Fin q × Fin 1 → K) = 0
  rw [Pi.zero_apply, zero_smul]

private lemma toMM_blockProj_at1_T (K : Type u) [Field K] (q : ℕ) :
    (toMM K q ⟨1, by omega⟩)
      ((cwCanonicalGrading q (K := K)).blockProj ⟨1, by omega⟩ 1
        (Pi.single (⟨q+1, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K)) = 0 := by
  classical
  refine (toMM1_apply K q _).trans ?_
  have hmem : (Pi.single (⟨q+1, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K) ∈
      cwGradePiece K q 2 := by
    have h := single_mem_cwGradePiece (K := K) q (⟨q+1, by omega⟩ : Fin (q+2))
    rw [typeOfCW_qPlusOne] at h; exact h
  have hne : (2 : Fin 3) ≠ 1 := by decide
  rw [cw_subtype_blockProj_ne_1 q hne
      (Pi.single (⟨q+1, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K) hmem]
  apply Finset.sum_eq_zero
  intros j _
  show ((0 : Fin (q+2) → K) ⟨j.val+1, by omega⟩ : K) •
        (Pi.single (j, 0) 1 : Fin q × Fin 1 → K) = 0
  rw [Pi.zero_apply, zero_smul]

/-- σ_110 2 = 0 (class 0), eval at 0. -/
private lemma toMM_blockProj_at2 (K : Type u) [Field K] (q : ℕ)
    (a : Fin (q+2)) :
    (toMM K q ⟨2, by omega⟩)
      ((cwCanonicalGrading q (K := K)).blockProj ⟨2, by omega⟩ 0
        (Pi.single a (1 : K) : Fin (q+2) → K)) =
      ((Pi.single a (1 : K) : Fin (q+2) → K) ⟨0, by omega⟩) •
        (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) := by
  classical
  refine (toMM2_apply K q _).trans ?_
  by_cases ha : typeOfCW q a = 0
  · have hmem : (Pi.single a (1 : K) : Fin (q+2) → K) ∈ cwGradePiece K q 0 := by
      have := single_mem_cwGradePiece (K := K) q a
      rw [ha] at this; exact this
    rw [cw_subtype_blockProj_self_2 q 0
        (Pi.single a (1 : K) : Fin (q+2) → K) hmem]
  · have hmem : (Pi.single a (1 : K) : Fin (q+2) → K) ∈ cwGradePiece K q (typeOfCW q a) :=
      single_mem_cwGradePiece (K := K) q a
    have hne : (typeOfCW q a) ≠ (0 : Fin 3) := ha
    rw [cw_subtype_blockProj_ne_2 q hne
        (Pi.single a (1 : K) : Fin (q+2) → K) hmem]
    have ha0 : a.val ≠ 0 := by
      intro h; apply ha; simp [typeOfCW, h]
    have hpi : (Pi.single a (1 : K) : Fin (q+2) → K) ⟨0, by omega⟩ = 0 := by
      rw [Pi.single_apply]
      have hne0 : (⟨0, by omega⟩ : Fin (q+2)) ≠ a := by
        intro heq; apply ha0
        have := congrArg Fin.val heq.symm; simpa using this
      rw [if_neg hne0]
    rw [hpi]; simp
    try rfl

/-! ## The composite `gMap`. -/

private noncomputable def gMap (K : Type u) [Field K] (q : ℕ) :
    ∀ i : Fin 3, (CWObj K q).V i →ₗ[K] (MMObj K 1 q 1).V i :=
  fun i => (toMM K q i).comp ((cwCanonicalGrading q (K := K)).blockProj i (σ_110 i))

private lemma map_toMM_block_eq_map_g (K : Type u) [Field K] (q : ℕ) :
    PiTensorProduct.map (toMM K q)
      ((cwCanonicalGrading q (K := K)).blockSubtensor σ_110).t =
    PiTensorProduct.map (gMap K q) (CWTensor K q) := by
  show PiTensorProduct.map (toMM K q)
      ((cwCanonicalGrading q (K := K)).blockTensor σ_110) =
    PiTensorProduct.map (gMap K q) (CWTensor K q)
  unfold TensorObj.TypeGrading.blockTensor
  show ((PiTensorProduct.map (toMM K q)) ∘ₗ
      (PiTensorProduct.map (fun i => (cwCanonicalGrading q (K := K)).blockProj i (σ_110 i))))
        (CWObj K q).t = _
  exact congrFun (congrArg DFunLike.coe (PiTensorProduct.map_comp _ _).symm) _

/-! ## MMO survives; other monomials vanish. -/

private lemma gMap_CWMonom_MMO (K : Type u) [Field K] (q : ℕ) (i : Fin q) :
    PiTensorProduct.map (gMap K q)
      (CWMonom K q (⟨i.val+1, by omega⟩ : Fin (q+2))
        (⟨i.val+1, by omega⟩ : Fin (q+2))
        (⟨0, by omega⟩ : Fin (q+2))) =
      tprod K (fun s : Fin 3 =>
        match s with
        | ⟨0, _⟩ => (Pi.single (0, i) 1 : Fin 1 × Fin q → K)
        | ⟨1, _⟩ => (Pi.single (i, 0) 1 : Fin q × Fin 1 → K)
        | ⟨2, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)) := by
  unfold CWMonom
  erw [PiTensorProduct.map_tprod]
  have hfun : (fun s : Fin 3 =>
        gMap K q s
          (match s with
            | ⟨0, _⟩ => (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K)
            | ⟨1, _⟩ => (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K)
            | ⟨2, _⟩ => (Pi.single (⟨0, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K))) =
      (fun s : Fin 3 =>
        match s with
        | ⟨0, _⟩ => (Pi.single (0, i) 1 : Fin 1 × Fin q → K)
        | ⟨1, _⟩ => (Pi.single (i, 0) 1 : Fin q × Fin 1 → K)
        | ⟨2, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)) := by
    funext s
    match s with
    | ⟨0, _⟩ =>
      show gMap K q ⟨0, _⟩ (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) 1) = _
      unfold gMap
      show (toMM K q ⟨0, by omega⟩) (((cwCanonicalGrading q).blockProj ⟨0, by omega⟩ 1)
        (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) 1)) = _
      exact toMM_blockProj_at0_M K q i
    | ⟨1, _⟩ =>
      show gMap K q ⟨1, _⟩ (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) 1) = _
      unfold gMap
      show (toMM K q ⟨1, by omega⟩) (((cwCanonicalGrading q).blockProj ⟨1, by omega⟩ 1)
        (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) 1)) = _
      exact toMM_blockProj_at1_M K q i
    | ⟨2, _⟩ =>
      show gMap K q ⟨2, _⟩ (Pi.single (⟨0, by omega⟩ : Fin (q+2)) 1) = _
      unfold gMap
      show (toMM K q ⟨2, by omega⟩) (((cwCanonicalGrading q).blockProj ⟨2, by omega⟩ 0)
        (Pi.single (⟨0, by omega⟩ : Fin (q+2)) 1)) = _
      rw [toMM_blockProj_at2]
      simp [Pi.single_eq_same]
      try rfl
  show (PiTensorProduct.tprod K) (fun s : Fin 3 =>
        gMap K q s
          (match s with
            | ⟨0, _⟩ => (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K)
            | ⟨1, _⟩ => (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K)
            | ⟨2, _⟩ => (Pi.single (⟨0, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K))) = _
  have h_lhs := congrArg (fun f => (PiTensorProduct.tprod K) f) hfun
  exact h_lhs

/-- OMM vanishing: mode 0 has e_O (class 0), σ wants class 1 → 0. -/
private lemma gMap_CWMonom_OMM (K : Type u) [Field K] (q : ℕ) (i : Fin q) :
    PiTensorProduct.map (gMap K q)
      (CWMonom K q (⟨0, by omega⟩ : Fin (q+2))
        (⟨i.val+1, by omega⟩ : Fin (q+2))
        (⟨i.val+1, by omega⟩ : Fin (q+2))) = 0 := by
  unfold CWMonom
  erw [PiTensorProduct.map_tprod]
  have h0 : gMap K q ⟨0, by omega⟩ (Pi.single (⟨0, by omega⟩ : Fin (q+2)) 1) = 0 := by
    unfold gMap
    show (toMM K q ⟨0, by omega⟩) (((cwCanonicalGrading q).blockProj ⟨0, by omega⟩ 1)
        (Pi.single (⟨0, by omega⟩ : Fin (q+2)) 1)) = _
    exact toMM_blockProj_at0_O K q
  show (PiTensorProduct.tprod K) (fun s : Fin 3 =>
        gMap K q s
          (match s with
            | ⟨0, _⟩ => (Pi.single (⟨0, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K)
            | ⟨1, _⟩ => (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K)
            | ⟨2, _⟩ => (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K))) = 0
  let f : ∀ s : Fin 3, (MMObj K 1 q 1).V s := fun s =>
    gMap K q s
      (match s with
        | ⟨0, _⟩ => (Pi.single (⟨0, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K)
        | ⟨1, _⟩ => (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K)
        | ⟨2, _⟩ => (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K))
  show (PiTensorProduct.tprod K) f = 0
  have hf0 : f (⟨0, by omega⟩ : Fin 3) = 0 := h0
  exact MultilinearMap.map_coord_zero (PiTensorProduct.tprod K) (⟨0, by omega⟩ : Fin 3) hf0

/-- MOM vanishing: mode 1 has e_O (class 0), σ wants class 1 → 0. -/
private lemma gMap_CWMonom_MOM (K : Type u) [Field K] (q : ℕ) (i : Fin q) :
    PiTensorProduct.map (gMap K q)
      (CWMonom K q (⟨i.val+1, by omega⟩ : Fin (q+2))
        (⟨0, by omega⟩ : Fin (q+2))
        (⟨i.val+1, by omega⟩ : Fin (q+2))) = 0 := by
  unfold CWMonom
  erw [PiTensorProduct.map_tprod]
  have h1 : gMap K q ⟨1, by omega⟩ (Pi.single (⟨0, by omega⟩ : Fin (q+2)) 1) = 0 := by
    unfold gMap
    show (toMM K q ⟨1, by omega⟩) (((cwCanonicalGrading q).blockProj ⟨1, by omega⟩ 1)
        (Pi.single (⟨0, by omega⟩ : Fin (q+2)) 1)) = _
    exact toMM_blockProj_at1_O K q
  show (PiTensorProduct.tprod K) (fun s : Fin 3 =>
        gMap K q s
          (match s with
            | ⟨0, _⟩ => (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K)
            | ⟨1, _⟩ => (Pi.single (⟨0, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K)
            | ⟨2, _⟩ => (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K))) = 0
  let f : ∀ s : Fin 3, (MMObj K 1 q 1).V s := fun s =>
    gMap K q s
      (match s with
        | ⟨0, _⟩ => (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K)
        | ⟨1, _⟩ => (Pi.single (⟨0, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K)
        | ⟨2, _⟩ => (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K))
  show (PiTensorProduct.tprod K) f = 0
  have hf1 : f (⟨1, by omega⟩ : Fin 3) = 0 := h1
  exact MultilinearMap.map_coord_zero (PiTensorProduct.tprod K) (⟨1, by omega⟩ : Fin 3) hf1

/-- OOT vanishing: mode 2 has e_T (class 2), σ wants class 0 → 0. -/
private lemma gMap_CWMonom_OOT (K : Type u) [Field K] (q : ℕ) :
    PiTensorProduct.map (gMap K q)
      (CWMonom K q (⟨0, by omega⟩ : Fin (q+2))
        (⟨0, by omega⟩ : Fin (q+2))
        (⟨q+1, by omega⟩ : Fin (q+2))) = 0 := by
  unfold CWMonom
  erw [PiTensorProduct.map_tprod]
  have h2 : gMap K q ⟨2, by omega⟩ (Pi.single (⟨q+1, by omega⟩ : Fin (q+2)) 1) = 0 := by
    unfold gMap
    show (toMM K q ⟨2, by omega⟩) (((cwCanonicalGrading q).blockProj ⟨2, by omega⟩ 0)
        (Pi.single (⟨q+1, by omega⟩ : Fin (q+2)) 1)) = _
    rw [toMM_blockProj_at2]
    have hne : (⟨0, by omega⟩ : Fin (q+2)) ≠ (⟨q+1, by omega⟩ : Fin (q+2)) := by
      intro heq
      have h := congrArg Fin.val heq
      simp at h
    have hp : (Pi.single (⟨q+1, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K) ⟨0, by omega⟩ = 0 :=
      Pi.single_eq_of_ne hne 1
    rw [hp, zero_smul]
    rfl
  show (PiTensorProduct.tprod K) (fun s : Fin 3 =>
        gMap K q s
          (match s with
            | ⟨0, _⟩ => (Pi.single (⟨0, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K)
            | ⟨1, _⟩ => (Pi.single (⟨0, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K)
            | ⟨2, _⟩ => (Pi.single (⟨q+1, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K))) = 0
  let f : ∀ s : Fin 3, (MMObj K 1 q 1).V s := fun s =>
    gMap K q s
      (match s with
        | ⟨0, _⟩ => (Pi.single (⟨0, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K)
        | ⟨1, _⟩ => (Pi.single (⟨0, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K)
        | ⟨2, _⟩ => (Pi.single (⟨q+1, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K))
  show (PiTensorProduct.tprod K) f = 0
  have hf2 : f (⟨2, by omega⟩ : Fin 3) = 0 := h2
  exact MultilinearMap.map_coord_zero (PiTensorProduct.tprod K) (⟨2, by omega⟩ : Fin 3) hf2

/-- OTO vanishing: mode 0 has e_O (class 0), σ wants class 1 → 0. -/
private lemma gMap_CWMonom_OTO (K : Type u) [Field K] (q : ℕ) :
    PiTensorProduct.map (gMap K q)
      (CWMonom K q (⟨0, by omega⟩ : Fin (q+2))
        (⟨q+1, by omega⟩ : Fin (q+2))
        (⟨0, by omega⟩ : Fin (q+2))) = 0 := by
  unfold CWMonom
  erw [PiTensorProduct.map_tprod]
  have h0 : gMap K q ⟨0, by omega⟩ (Pi.single (⟨0, by omega⟩ : Fin (q+2)) 1) = 0 := by
    unfold gMap
    show (toMM K q ⟨0, by omega⟩) (((cwCanonicalGrading q).blockProj ⟨0, by omega⟩ 1)
        (Pi.single (⟨0, by omega⟩ : Fin (q+2)) 1)) = _
    exact toMM_blockProj_at0_O K q
  show (PiTensorProduct.tprod K) (fun s : Fin 3 =>
        gMap K q s
          (match s with
            | ⟨0, _⟩ => (Pi.single (⟨0, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K)
            | ⟨1, _⟩ => (Pi.single (⟨q+1, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K)
            | ⟨2, _⟩ => (Pi.single (⟨0, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K))) = 0
  let f : ∀ s : Fin 3, (MMObj K 1 q 1).V s := fun s =>
    gMap K q s
      (match s with
        | ⟨0, _⟩ => (Pi.single (⟨0, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K)
        | ⟨1, _⟩ => (Pi.single (⟨q+1, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K)
        | ⟨2, _⟩ => (Pi.single (⟨0, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K))
  show (PiTensorProduct.tprod K) f = 0
  have hf0 : f (⟨0, by omega⟩ : Fin 3) = 0 := h0
  exact MultilinearMap.map_coord_zero (PiTensorProduct.tprod K) (⟨0, by omega⟩ : Fin 3) hf0

/-- TOO vanishing: mode 0 has e_T (class 2), σ wants class 1 → 0. -/
private lemma gMap_CWMonom_TOO (K : Type u) [Field K] (q : ℕ) :
    PiTensorProduct.map (gMap K q)
      (CWMonom K q (⟨q+1, by omega⟩ : Fin (q+2))
        (⟨0, by omega⟩ : Fin (q+2))
        (⟨0, by omega⟩ : Fin (q+2))) = 0 := by
  unfold CWMonom
  erw [PiTensorProduct.map_tprod]
  have h0 : gMap K q ⟨0, by omega⟩ (Pi.single (⟨q+1, by omega⟩ : Fin (q+2)) 1) = 0 := by
    unfold gMap
    show (toMM K q ⟨0, by omega⟩) (((cwCanonicalGrading q).blockProj ⟨0, by omega⟩ 1)
        (Pi.single (⟨q+1, by omega⟩ : Fin (q+2)) 1)) = _
    exact toMM_blockProj_at0_T K q
  show (PiTensorProduct.tprod K) (fun s : Fin 3 =>
        gMap K q s
          (match s with
            | ⟨0, _⟩ => (Pi.single (⟨q+1, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K)
            | ⟨1, _⟩ => (Pi.single (⟨0, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K)
            | ⟨2, _⟩ => (Pi.single (⟨0, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K))) = 0
  let f : ∀ s : Fin 3, (MMObj K 1 q 1).V s := fun s =>
    gMap K q s
      (match s with
        | ⟨0, _⟩ => (Pi.single (⟨q+1, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K)
        | ⟨1, _⟩ => (Pi.single (⟨0, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K)
        | ⟨2, _⟩ => (Pi.single (⟨0, by omega⟩ : Fin (q+2)) 1 : Fin (q+2) → K))
  show (PiTensorProduct.tprod K) f = 0
  have hf0 : f (⟨0, by omega⟩ : Fin 3) = 0 := h0
  exact MultilinearMap.map_coord_zero (PiTensorProduct.tprod K) (⟨0, by omega⟩ : Fin 3) hf0

end MMECWBlockAt110Sol

open MMECWBlockAt110Sol

theorem solution {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict
      (MMObj K 1 q 1)
      ((cwCanonicalGrading q (K := K)).blockSubtensor
        (fun i : Fin 3 =>
          match i with
          | ⟨0, _⟩ => 1
          | ⟨1, _⟩ => 1
          | ⟨2, _⟩ => 0)) := by
  refine ⟨MMECWBlockAt110Sol.toMM K q, ?_⟩
  show PiTensorProduct.map (MMECWBlockAt110Sol.toMM K q)
      ((cwCanonicalGrading q (K := K)).blockSubtensor MMECWBlockAt110Sol.σ_110).t =
      MMTensor K 1 q 1
  rw [map_toMM_block_eq_map_g]
  set O : Fin (q+2) := ⟨0, by omega⟩ with hO
  set T : Fin (q+2) := ⟨q+1, by omega⟩ with hT
  show PiTensorProduct.map (gMap K q)
      ((∑ i : Fin q,
          (CWMonom K q O
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2))
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) +
            CWMonom K q (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) O
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) +
            CWMonom K q (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2))
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) O)) +
        CWMonom K q O O T + CWMonom K q O T O + CWMonom K q T O O) = MMTensor K 1 q 1
  set F := PiTensorProduct.map (gMap K q) with hF
  set innerSum : PiTensorProduct K (CWSpace K q) := ∑ i : Fin q,
        (CWMonom K q O
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2))
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) +
            CWMonom K q (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) O
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) +
            CWMonom K q (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2))
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) O) with hInnerSum
  set bOOT : PiTensorProduct K (CWSpace K q) := CWMonom K q O O T with hbOOT
  set bOTO : PiTensorProduct K (CWSpace K q) := CWMonom K q O T O with hbOTO
  set bTOO : PiTensorProduct K (CWSpace K q) := CWMonom K q T O O with hbTOO
  suffices h : F innerSum + F bOOT + F bOTO + F bTOO = MMTensor K 1 q 1 by
    have rewrt : F (innerSum + bOOT + bOTO + bTOO) =
        F innerSum + F bOOT + F bOTO + F bTOO := by
      have eq1 : F ((innerSum + bOOT + bOTO) + bTOO) = F (innerSum + bOOT + bOTO) + F bTOO :=
        LinearMap.map_add F _ _
      have eq2 : F ((innerSum + bOOT) + bOTO) = F (innerSum + bOOT) + F bOTO :=
        LinearMap.map_add F _ _
      have eq3 : F (innerSum + bOOT) = F innerSum + F bOOT :=
        LinearMap.map_add F _ _
      calc F (innerSum + bOOT + bOTO + bTOO)
          = F (innerSum + bOOT + bOTO) + F bTOO := eq1
        _ = (F (innerSum + bOOT) + F bOTO) + F bTOO := by rw [eq2]
        _ = ((F innerSum + F bOOT) + F bOTO) + F bTOO := by rw [eq3]
    rw [rewrt]
    exact h
  rw [show F innerSum = ∑ i : Fin q, F (CWMonom K q O
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2))
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) +
            CWMonom K q (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) O
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) +
            CWMonom K q (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2))
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) O) from by
      rw [hInnerSum]
      exact _root_.map_sum F _ Finset.univ]
  have hF_triple : ∀ i : Fin q,
      F (CWMonom K q O
            (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2))
            (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) +
          CWMonom K q (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) O
            (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) +
          CWMonom K q (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2))
            (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) O) =
      tprod K (fun s : Fin 3 =>
        match s with
        | ⟨0, _⟩ => (Pi.single (0, i) 1 : Fin 1 × Fin q → K)
        | ⟨1, _⟩ => (Pi.single (i, 0) 1 : Fin q × Fin 1 → K)
        | ⟨2, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)) := by
    intro i
    set M : Fin (q+2) := ⟨(i : Fin q).val + 1, by omega⟩ with hM
    have hsum : F (CWMonom K q O M M + CWMonom K q M O M + CWMonom K q M M O) =
        F (CWMonom K q O M M) + F (CWMonom K q M O M) + F (CWMonom K q M M O) := by
      have e1 : F ((CWMonom K q O M M + CWMonom K q M O M) + CWMonom K q M M O) =
          F (CWMonom K q O M M + CWMonom K q M O M) + F (CWMonom K q M M O) :=
        LinearMap.map_add F _ _
      have e2 : F (CWMonom K q O M M + CWMonom K q M O M) =
          F (CWMonom K q O M M) + F (CWMonom K q M O M) :=
        LinearMap.map_add F _ _
      calc F (CWMonom K q O M M + CWMonom K q M O M + CWMonom K q M M O)
          = F (CWMonom K q O M M + CWMonom K q M O M) + F (CWMonom K q M M O) := e1
        _ = (F (CWMonom K q O M M) + F (CWMonom K q M O M)) + F (CWMonom K q M M O) := by rw [e2]
    rw [hsum]
    rw [hO, hM, hF]
    rw [gMap_CWMonom_OMM K q i, gMap_CWMonom_MOM K q i, gMap_CWMonom_MMO K q i]
    simp
  rw [show (∑ i : Fin q, F (CWMonom K q O
          (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2))
          (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) +
        CWMonom K q (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) O
          (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) +
        CWMonom K q (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2))
          (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) O)) =
      ∑ i : Fin q, tprod K (fun s : Fin 3 =>
        match s with
        | ⟨0, _⟩ => (Pi.single (0, i) 1 : Fin 1 × Fin q → K)
        | ⟨1, _⟩ => (Pi.single (i, 0) 1 : Fin q × Fin 1 → K)
        | ⟨2, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)) from by
      apply Finset.sum_congr rfl
      intros i _
      exact hF_triple i]
  rw [show F (CWMonom K q O O T) = 0 from by
      rw [show O = (⟨0, by omega⟩ : Fin (q+2)) from rfl]
      rw [show T = (⟨q+1, by omega⟩ : Fin (q+2)) from rfl]
      exact gMap_CWMonom_OOT K q]
  rw [show F (CWMonom K q O T O) = 0 from by
      rw [show O = (⟨0, by omega⟩ : Fin (q+2)) from rfl]
      rw [show T = (⟨q+1, by omega⟩ : Fin (q+2)) from rfl]
      exact gMap_CWMonom_OTO K q]
  rw [show F (CWMonom K q T O O) = 0 from by
      rw [show O = (⟨0, by omega⟩ : Fin (q+2)) from rfl]
      rw [show T = (⟨q+1, by omega⟩ : Fin (q+2)) from rfl]
      exact gMap_CWMonom_TOO K q]
  simp only [add_zero]
  unfold MMTensor
  -- MMTensor K 1 q 1 = ∑ i : Fin 1, ∑ j : Fin q, ∑ k : Fin 1, tprod (...).
  rw [Fin.sum_univ_one]
  apply Finset.sum_congr rfl
  intros j _
  rw [Fin.sum_univ_one]
  rfl
