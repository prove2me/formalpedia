-- Prove2me | solution 1 for mme_CW_block_is_MM_at_002
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-06-05T02:05:12.009491+00:00
-- url     : https://prove2.me/submissions/46f8184e-9f42-47c3-a1b1-d236e481d96d

import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Definitions.Def_mme_block_subtensor
import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_CW_canonical_grading
import Definitions.Def_mme_tensor_rank
import Definitions.Def_mme_tensor_type_grading
import Definitions.Def_mme_omega

open MME



/-! # `Sol_mme_CW_block_is_MM_at_002` — closes `mme_CW_block_is_MM_at_002`.

For the canonical 3-grading on `CWObj K q`, the σ-block at σ = (0,0,2) extracts
the single rank-one term `e_O ⊗ e_O ⊗ e_T` from `T_q`, which after class-
isomorphism is `MMObj K 1 1 1`.

Strategy:
* `block.t = PiTensorProduct.map (blockProj₀, blockProj₀, blockProj₂) CWTensor`.
* Compose with f : (block).V i →ₗ[K] (MMObj K 1 1 1).V i sending each class-
  element to `Pi.single (0, 0) (eval at boundary index)`.
* The composite `f ∘ blockProj` annihilates all monomials of T_q except
  `e_O ⊗ e_O ⊗ e_T`, mapping that one to `MMPure K 1 1 1 0 0 0 = MMTensor K 1 1 1`.

Status: LOCAL ONLY. Validation gate for the corrected design. -/

set_option maxHeartbeats 1200000

open MME PiTensorProduct BigOperators

universe u

namespace MMECWBlockAt002Sol

variable {K : Type u} [Field K] {q : ℕ}

/-- The σ-target for the (0, 0, 2) case. -/
def σ_002 : Fin 3 → Fin 3 := fun i =>
  match i with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 2

/-- The Restrict witness: a per-mode linear map from the block to MMObj K 1 1 1. -/
noncomputable def toMM (K : Type u) [Field K] (q : ℕ) :
    ∀ i : Fin 3,
      ((cwCanonicalGrading q (K := K)).blockSubtensor σ_002).V i →ₗ[K]
        (MMObj K 1 1 1).V i :=
  fun i =>
    match i with
    | ⟨0, _⟩ =>
      LinearMap.smulRight
        ((LinearMap.proj (⟨0, by omega⟩ : Fin (q+2)) :
            (Fin (q+2) → K) →ₗ[K] K).comp
          (Submodule.subtype (cwGradePiece K q 0)))
        (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
    | ⟨1, _⟩ =>
      LinearMap.smulRight
        ((LinearMap.proj (⟨0, by omega⟩ : Fin (q+2)) :
            (Fin (q+2) → K) →ₗ[K] K).comp
          (Submodule.subtype (cwGradePiece K q 0)))
        (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
    | ⟨2, _⟩ =>
      LinearMap.smulRight
        ((LinearMap.proj (⟨q+1, by omega⟩ : Fin (q+2)) :
            (Fin (q+2) → K) →ₗ[K] K).comp
          (Submodule.subtype (cwGradePiece K q 2)))
        (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)

/-! ## blockProj evaluation helpers (re-derived locally)

These mirror the private helpers in
`Theorems/Thm_mme_independent_blocks_form_direct_sum_restrict_enum.lean`. -/

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

/-- For `v ∈ G.classOf i α`, `(G.classOf i α).subtype (blockProj G i α v) = v`. -/
private lemma subtype_blockProj_self {d t : ℕ} {T : TensorObj K d}
    (G : T.TypeGrading t)
    (i : Fin d) (α : Fin t) (v : T.V i) (hv : v ∈ G.classOf i α) :
    (G.classOf i α).subtype (G.blockProj i α v) = v := by
  rw [blockProj_eq_aux, modeLequiv_symm_apply_aux]
  show ((((LinearEquiv.ofBijective
        (DirectSum.coeLinearMap fun β => (G.classOf i β : Submodule K (T.V i)))
        (G.is_internal i)).symm v) α : G.classOf i α) : T.V i) = v
  rw [DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem (G.is_internal i) hv]

/-- For `v ∈ G.classOf i α` and `α ≠ α'`, `(G.classOf i α').subtype (blockProj G i α' v) = 0`. -/
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

/-- Specialization at the canonical grading, mode 0. -/
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

/-! ## Pointwise evaluation of `toMM ∘ blockProj` on a basis vector `Pi.single a 1`.

We compute the result in three modes. The key observation: for mode 0/1, the
target class is 0 (i.e. cwGradePiece K q 0), and the toMM evaluates the subtype
of blockProj at index 0. For mode 2, target class is 2 and evaluation is at q+1. -/

/-- Compact form of `toMM K q ⟨0, _⟩` applied to a class-0 element. -/
private lemma toMM0_apply (K : Type u) [Field K] (q : ℕ)
    (w : cwGradePiece K q 0) :
    toMM K q ⟨0, by omega⟩ w =
      ((cwGradePiece K q 0).subtype w ⟨0, by omega⟩) •
        (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) := by
  show LinearMap.smulRight ((LinearMap.proj (⟨0, by omega⟩ : Fin (q+2)) :
        (Fin (q+2) → K) →ₗ[K] K).comp
        (Submodule.subtype (cwGradePiece K q 0)))
      (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) w = _
  rw [LinearMap.smulRight_apply, LinearMap.comp_apply, LinearMap.proj_apply]

/-- Compact form of `toMM K q ⟨1, _⟩` applied to a class-0 element. -/
private lemma toMM1_apply (K : Type u) [Field K] (q : ℕ)
    (w : cwGradePiece K q 0) :
    toMM K q ⟨1, by omega⟩ w =
      ((cwGradePiece K q 0).subtype w ⟨0, by omega⟩) •
        (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) := by
  show LinearMap.smulRight ((LinearMap.proj (⟨0, by omega⟩ : Fin (q+2)) :
        (Fin (q+2) → K) →ₗ[K] K).comp
        (Submodule.subtype (cwGradePiece K q 0)))
      (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) w = _
  rw [LinearMap.smulRight_apply, LinearMap.comp_apply, LinearMap.proj_apply]

/-- Compact form of `toMM K q ⟨2, _⟩` applied to a class-2 element. -/
private lemma toMM2_apply (K : Type u) [Field K] (q : ℕ)
    (w : cwGradePiece K q 2) :
    toMM K q ⟨2, by omega⟩ w =
      ((cwGradePiece K q 2).subtype w ⟨q+1, by omega⟩) •
        (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) := by
  show LinearMap.smulRight ((LinearMap.proj (⟨q+1, by omega⟩ : Fin (q+2)) :
        (Fin (q+2) → K) →ₗ[K] K).comp
        (Submodule.subtype (cwGradePiece K q 2)))
      (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) w = _
  rw [LinearMap.smulRight_apply, LinearMap.comp_apply, LinearMap.proj_apply]

/-- For mode 0, σ_002 0 = 0, so the composite `toMM_0 ∘ blockProj_0 0` evaluates a basis
vector `Pi.single a 1` to `(Pi.single a 1) ⟨0, _⟩ • Pi.single (0,0) 1`. -/
private lemma toMM_blockProj_at0 (K : Type u) [Field K] (q : ℕ)
    (a : Fin (q+2)) :
    (toMM K q ⟨0, by omega⟩)
      ((cwCanonicalGrading q (K := K)).blockProj ⟨0, by omega⟩ 0
        (Pi.single a (1 : K) : Fin (q+2) → K)) =
      ((Pi.single a (1 : K) : Fin (q+2) → K) ⟨0, by omega⟩) •
        (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) := by
  classical
  refine (toMM0_apply K q _).trans ?_
  -- Goal: (cwGradePiece K q 0).subtype (blockProj ⟨0,_⟩ 0 (Pi.single a 1)) ⟨0,_⟩ • Pi.single (0,0) 1
  --     = (Pi.single a 1) ⟨0,_⟩ • Pi.single (0,0) 1
  by_cases ha : typeOfCW q a = 0
  · have hmem : (Pi.single a (1 : K) : Fin (q+2) → K) ∈ cwGradePiece K q 0 := by
      have := single_mem_cwGradePiece (K := K) q a
      rw [ha] at this; exact this
    rw [cw_subtype_blockProj_self_0 q 0
        (Pi.single a (1 : K) : Fin (q+2) → K) hmem]
  · have hmem : (Pi.single a (1 : K) : Fin (q+2) → K) ∈ cwGradePiece K q (typeOfCW q a) :=
      single_mem_cwGradePiece (K := K) q a
    have hne : (typeOfCW q a) ≠ (0 : Fin 3) := ha
    rw [cw_subtype_blockProj_ne_0 q hne
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

/-- Mode-1 version. -/
private lemma toMM_blockProj_at1 (K : Type u) [Field K] (q : ℕ)
    (a : Fin (q+2)) :
    (toMM K q ⟨1, by omega⟩)
      ((cwCanonicalGrading q (K := K)).blockProj ⟨1, by omega⟩ 0
        (Pi.single a (1 : K) : Fin (q+2) → K)) =
      ((Pi.single a (1 : K) : Fin (q+2) → K) ⟨0, by omega⟩) •
        (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) := by
  classical
  refine (toMM1_apply K q _).trans ?_
  by_cases ha : typeOfCW q a = 0
  · have hmem : (Pi.single a (1 : K) : Fin (q+2) → K) ∈ cwGradePiece K q 0 := by
      have := single_mem_cwGradePiece (K := K) q a
      rw [ha] at this; exact this
    rw [cw_subtype_blockProj_self_1 q 0
        (Pi.single a (1 : K) : Fin (q+2) → K) hmem]
  · have hmem : (Pi.single a (1 : K) : Fin (q+2) → K) ∈ cwGradePiece K q (typeOfCW q a) :=
      single_mem_cwGradePiece (K := K) q a
    have hne : (typeOfCW q a) ≠ (0 : Fin 3) := ha
    rw [cw_subtype_blockProj_ne_1 q hne
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

/-- Mode-2 version: σ_002 2 = 2 and the projection is at index q+1. -/
private lemma toMM_blockProj_at2 (K : Type u) [Field K] (q : ℕ)
    (a : Fin (q+2)) :
    (toMM K q ⟨2, by omega⟩)
      ((cwCanonicalGrading q (K := K)).blockProj ⟨2, by omega⟩ 2
        (Pi.single a (1 : K) : Fin (q+2) → K)) =
      ((Pi.single a (1 : K) : Fin (q+2) → K) ⟨q+1, by omega⟩) •
        (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) := by
  classical
  refine (toMM2_apply K q _).trans ?_
  by_cases ha : typeOfCW q a = 2
  · have hmem : (Pi.single a (1 : K) : Fin (q+2) → K) ∈ cwGradePiece K q 2 := by
      have := single_mem_cwGradePiece (K := K) q a
      rw [ha] at this; exact this
    rw [cw_subtype_blockProj_self_2 q 2
        (Pi.single a (1 : K) : Fin (q+2) → K) hmem]
  · have hmem : (Pi.single a (1 : K) : Fin (q+2) → K) ∈ cwGradePiece K q (typeOfCW q a) :=
      single_mem_cwGradePiece (K := K) q a
    have hne : (typeOfCW q a) ≠ (2 : Fin 3) := ha
    rw [cw_subtype_blockProj_ne_2 q hne
        (Pi.single a (1 : K) : Fin (q+2) → K) hmem]
    have haq1 : a.val ≠ q + 1 := by
      intro h; apply ha; simp [typeOfCW, h]
    have hpi : (Pi.single a (1 : K) : Fin (q+2) → K) ⟨q+1, by omega⟩ = 0 := by
      rw [Pi.single_apply]
      have hneq1 : (⟨q+1, by omega⟩ : Fin (q+2)) ≠ a := by
        intro heq; apply haq1
        have := congrArg Fin.val heq.symm; simpa using this
      rw [if_neg hneq1]
    rw [hpi]; simp
    try rfl

/-! ## The composite `gMap i := toMM i ∘ blockProj i (σ_002 i)`. -/

/-- The composite linear map (mode-wise). -/
private noncomputable def gMap (K : Type u) [Field K] (q : ℕ) :
    ∀ i : Fin 3, (CWObj K q).V i →ₗ[K] (MMObj K 1 1 1).V i :=
  fun i => (toMM K q i).comp ((cwCanonicalGrading q (K := K)).blockProj i (σ_002 i))

/-- `map toMM (blockSubtensor σ_002).t = map gMap (CWTensor K q)`. -/
private lemma map_toMM_block_eq_map_g (K : Type u) [Field K] (q : ℕ) :
    PiTensorProduct.map (toMM K q)
      ((cwCanonicalGrading q (K := K)).blockSubtensor σ_002).t =
    PiTensorProduct.map (gMap K q) (CWTensor K q) := by
  show PiTensorProduct.map (toMM K q)
      ((cwCanonicalGrading q (K := K)).blockTensor σ_002) =
    PiTensorProduct.map (gMap K q) (CWTensor K q)
  unfold TensorObj.TypeGrading.blockTensor
  -- Goal: map toMM (map blockProj (CWObj K q).t) = map gMap (CWTensor K q).
  -- (CWObj K q).t = CWTensor K q definitionally.
  -- map composes: map toMM ∘ map blockProj = map (toMM ∘ blockProj) = map gMap.
  show ((PiTensorProduct.map (toMM K q)) ∘ₗ
      (PiTensorProduct.map (fun i => (cwCanonicalGrading q (K := K)).blockProj i (σ_002 i))))
        (CWObj K q).t = _
  exact congrFun (congrArg DFunLike.coe (PiTensorProduct.map_comp _ _).symm) _

/-! ## Evaluation of `gMap` on a CW monomial. -/

/-- The monomial `e_a ⊗ e_b ⊗ e_c` maps under `gMap` to the scaled pure tensor. -/
private lemma gMap_CWMonom (K : Type u) [Field K] (q : ℕ) (a b c : Fin (q+2)) :
    PiTensorProduct.map (gMap K q) (CWMonom K q a b c) =
      (((Pi.single a (1 : K) : Fin (q+2) → K) ⟨0, by omega⟩) *
        ((Pi.single b (1 : K) : Fin (q+2) → K) ⟨0, by omega⟩) *
        ((Pi.single c (1 : K) : Fin (q+2) → K) ⟨q+1, by omega⟩)) •
      tprod K (fun s : Fin 3 =>
        match s with
        | ⟨0, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
        | ⟨1, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
        | ⟨2, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)) := by
  unfold CWMonom
  erw [PiTensorProduct.map_tprod]
  set c0 : K := (Pi.single a (1 : K) : Fin (q+2) → K) ⟨0, by omega⟩ with hc0
  set c1 : K := (Pi.single b (1 : K) : Fin (q+2) → K) ⟨0, by omega⟩ with hc1
  set c2 : K := (Pi.single c (1 : K) : Fin (q+2) → K) ⟨q+1, by omega⟩ with hc2
  -- After map_tprod, LHS = tprod K (fun s => gMap s (factor s)).
  have hfun : (fun s : Fin 3 =>
        gMap K q s
          (match s with
            | ⟨0, _⟩ => (Pi.single a 1 : Fin (q+2) → K)
            | ⟨1, _⟩ => (Pi.single b 1 : Fin (q+2) → K)
            | ⟨2, _⟩ => (Pi.single c 1 : Fin (q+2) → K))) =
      (fun s : Fin 3 =>
        match s with
        | ⟨0, _⟩ => c0 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
        | ⟨1, _⟩ => c1 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
        | ⟨2, _⟩ => c2 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)) := by
    funext s
    match s with
    | ⟨0, _⟩ =>
      show gMap K q ⟨0, _⟩ (Pi.single a 1 : Fin (q+2) → K) = _
      unfold gMap
      show (toMM K q ⟨0, by omega⟩) (((cwCanonicalGrading q).blockProj ⟨0, by omega⟩ 0)
        (Pi.single a 1 : Fin (q+2) → K)) = _
      rw [toMM_blockProj_at0]
    | ⟨1, _⟩ =>
      show gMap K q ⟨1, _⟩ (Pi.single b 1 : Fin (q+2) → K) = _
      unfold gMap
      show (toMM K q ⟨1, by omega⟩) (((cwCanonicalGrading q).blockProj ⟨1, by omega⟩ 0)
        (Pi.single b 1 : Fin (q+2) → K)) = _
      rw [toMM_blockProj_at1]
    | ⟨2, _⟩ =>
      show gMap K q ⟨2, _⟩ (Pi.single c 1 : Fin (q+2) → K) = _
      unfold gMap
      show (toMM K q ⟨2, by omega⟩) (((cwCanonicalGrading q).blockProj ⟨2, by omega⟩ 2)
        (Pi.single c 1 : Fin (q+2) → K)) = _
      rw [toMM_blockProj_at2]
  -- Switch the binder to `s` to enable rewriting with hfun.
  show (PiTensorProduct.tprod K) (fun s : Fin 3 =>
        gMap K q s
          (match s with
            | ⟨0, _⟩ => (Pi.single a 1 : Fin (q+2) → K)
            | ⟨1, _⟩ => (Pi.single b 1 : Fin (q+2) → K)
            | ⟨2, _⟩ => (Pi.single c 1 : Fin (q+2) → K))) = _
  have h_lhs := congrArg (fun f => (PiTensorProduct.tprod K) f) hfun
  rw [h_lhs]
  -- Pull scalars out factor-by-factor via MultilinearMap.tprod's `map_smul`.
  -- Apply at coord 0: tprod (..., c0 • v0, ...) = c0 • tprod (..., v0, ...).
  let f0 : ∀ s : Fin 3, (MMObj K 1 1 1).V s := fun s =>
    match s with
    | ⟨0, _⟩ => c0 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
    | ⟨1, _⟩ => c1 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
    | ⟨2, _⟩ => c2 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
  let f1 : ∀ s : Fin 3, (MMObj K 1 1 1).V s := fun s =>
    match s with
    | ⟨0, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
    | ⟨1, _⟩ => c1 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
    | ⟨2, _⟩ => c2 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
  let f2 : ∀ s : Fin 3, (MMObj K 1 1 1).V s := fun s =>
    match s with
    | ⟨0, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
    | ⟨1, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
    | ⟨2, _⟩ => c2 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
  let f3 : ∀ s : Fin 3, (MMObj K 1 1 1).V s := fun s =>
    match s with
    | ⟨0, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
    | ⟨1, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
    | ⟨2, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
  -- f0 = Function.update f1 0 (c0 • single).
  have eq_f0 : f0 = Function.update f1 (⟨0, by omega⟩ : Fin 3)
        (c0 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)) := by
    funext s; match s with
    | ⟨0, _⟩ => simp [f0, Function.update]; try rfl
    | ⟨1, _⟩ => simp [f0, f1, Function.update]; try rfl
    | ⟨2, _⟩ => simp [f0, f1, Function.update]; try rfl
  have eq_f1 : Function.update f1 (⟨0, by omega⟩ : Fin 3)
        (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) =
      Function.update f2 (⟨1, by omega⟩ : Fin 3)
        (c1 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)) := by
    funext s; match s with
    | ⟨0, _⟩ => simp [f2, Function.update]; try rfl
    | ⟨1, _⟩ => simp [f1, Function.update]; try rfl
    | ⟨2, _⟩ => simp [f1, f2, Function.update]; try rfl
  have eq_f2 : Function.update f2 (⟨1, by omega⟩ : Fin 3)
        (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) =
      Function.update f3 (⟨2, by omega⟩ : Fin 3)
        (c2 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)) := by
    funext s; match s with
    | ⟨0, _⟩ => simp [f2, f3, Function.update]; try rfl
    | ⟨1, _⟩ => simp [f3, Function.update]; try rfl
    | ⟨2, _⟩ => simp [f2, Function.update]; try rfl
  have eq_f3 : Function.update f3 (⟨2, by omega⟩ : Fin 3)
        (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) = f3 := by
    funext s; match s with
    | ⟨0, _⟩ => simp [f3, Function.update]; try rfl
    | ⟨1, _⟩ => simp [f3, Function.update]; try rfl
    | ⟨2, _⟩ => simp [f3, Function.update]; try rfl
  -- Compute the chain.
  calc (PiTensorProduct.tprod K) (fun s : Fin 3 =>
        match s with
        | ⟨0, _⟩ => c0 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
        | ⟨1, _⟩ => c1 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
        | ⟨2, _⟩ => c2 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K))
      = (PiTensorProduct.tprod K) f0 := rfl
    _ = (PiTensorProduct.tprod K) (Function.update f1 (⟨0, by omega⟩ : Fin 3)
          (c0 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K))) := by rw [eq_f0]
    _ = c0 • (PiTensorProduct.tprod K)
          (Function.update f1 (⟨0, by omega⟩ : Fin 3)
            (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)) := by
        exact MultilinearMap.map_update_smul (PiTensorProduct.tprod K) f1
          (⟨0, by omega⟩ : Fin 3) c0
          (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
    _ = c0 • (PiTensorProduct.tprod K)
          (Function.update f2 (⟨1, by omega⟩ : Fin 3)
            (c1 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K))) := by rw [eq_f1]
    _ = c0 • (c1 • (PiTensorProduct.tprod K)
          (Function.update f2 (⟨1, by omega⟩ : Fin 3)
            (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K))) := by
        congr 1
        exact MultilinearMap.map_update_smul (PiTensorProduct.tprod K) f2
          (⟨1, by omega⟩ : Fin 3) c1
          (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
    _ = c0 • (c1 • (PiTensorProduct.tprod K)
          (Function.update f3 (⟨2, by omega⟩ : Fin 3)
            (c2 • (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)))) := by rw [eq_f2]
    _ = c0 • (c1 • (c2 • (PiTensorProduct.tprod K)
          (Function.update f3 (⟨2, by omega⟩ : Fin 3)
            (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)))) := by
        congr 1; congr 1
        exact MultilinearMap.map_update_smul (PiTensorProduct.tprod K) f3
          (⟨2, by omega⟩ : Fin 3) c2
          (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
    _ = c0 • (c1 • (c2 • (PiTensorProduct.tprod K) f3)) := by rw [eq_f3]
    _ = (c0 * c1 * c2) • (PiTensorProduct.tprod K) f3 := by
        rw [smul_smul, smul_smul]
    _ = (c0 * c1 * c2) • (PiTensorProduct.tprod K) (fun s : Fin 3 =>
          match s with
          | ⟨0, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
          | ⟨1, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
          | ⟨2, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)) := rfl

/-! ## Vanishing for non-OOT monomials, evaluation for OOT. -/

private lemma gMap_CWMonom_OOT (K : Type u) [Field K] (q : ℕ) :
    PiTensorProduct.map (gMap K q)
      (CWMonom K q (⟨0, by omega⟩ : Fin (q+2)) (⟨0, by omega⟩ : Fin (q+2))
        (⟨q+1, by omega⟩ : Fin (q+2))) =
      tprod K (fun s : Fin 3 =>
        match s with
        | ⟨0, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
        | ⟨1, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
        | ⟨2, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)) := by
  rw [gMap_CWMonom]
  simp [Pi.single_eq_same]

private lemma gMap_CWMonom_OMM (K : Type u) [Field K] (q : ℕ) (i : Fin q) :
    PiTensorProduct.map (gMap K q)
      (CWMonom K q (⟨0, by omega⟩ : Fin (q+2))
        (⟨i.val+1, by omega⟩ : Fin (q+2))
        (⟨i.val+1, by omega⟩ : Fin (q+2))) = 0 := by
  rw [gMap_CWMonom]
  have hb : (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K) ⟨0, by omega⟩ = 0 := by
    rw [Pi.single_apply]
    have : (⟨0, by omega⟩ : Fin (q+2)) ≠ ⟨i.val+1, by omega⟩ := by
      intro heq
      have := congrArg Fin.val heq
      simp at this
    simp
  rw [hb]; simp

private lemma gMap_CWMonom_MOM (K : Type u) [Field K] (q : ℕ) (i : Fin q) :
    PiTensorProduct.map (gMap K q)
      (CWMonom K q (⟨i.val+1, by omega⟩ : Fin (q+2))
        (⟨0, by omega⟩ : Fin (q+2))
        (⟨i.val+1, by omega⟩ : Fin (q+2))) = 0 := by
  rw [gMap_CWMonom]
  have ha : (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K) ⟨0, by omega⟩ = 0 := by
    rw [Pi.single_apply]
    have : (⟨0, by omega⟩ : Fin (q+2)) ≠ ⟨i.val+1, by omega⟩ := by
      intro heq
      have := congrArg Fin.val heq
      simp at this
    simp
  rw [ha]; simp

private lemma gMap_CWMonom_MMO (K : Type u) [Field K] (q : ℕ) (i : Fin q) :
    PiTensorProduct.map (gMap K q)
      (CWMonom K q (⟨i.val+1, by omega⟩ : Fin (q+2))
        (⟨i.val+1, by omega⟩ : Fin (q+2))
        (⟨0, by omega⟩ : Fin (q+2))) = 0 := by
  rw [gMap_CWMonom]
  have ha : (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K) ⟨0, by omega⟩ = 0 := by
    rw [Pi.single_apply]
    have : (⟨0, by omega⟩ : Fin (q+2)) ≠ ⟨i.val+1, by omega⟩ := by
      intro heq
      have := congrArg Fin.val heq
      simp at this
    simp
  rw [ha]; simp

private lemma gMap_CWMonom_OTO (K : Type u) [Field K] (q : ℕ) :
    PiTensorProduct.map (gMap K q)
      (CWMonom K q (⟨0, by omega⟩ : Fin (q+2))
        (⟨q+1, by omega⟩ : Fin (q+2))
        (⟨0, by omega⟩ : Fin (q+2))) = 0 := by
  rw [gMap_CWMonom]
  have hc : (Pi.single (⟨0, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K) ⟨q+1, by omega⟩ = 0 := by
    rw [Pi.single_apply]
    have : (⟨q+1, by omega⟩ : Fin (q+2)) ≠ ⟨0, by omega⟩ := by
      intro heq
      have := congrArg Fin.val heq
      simp at this
    simp
  rw [hc]; simp

private lemma gMap_CWMonom_TOO (K : Type u) [Field K] (q : ℕ) :
    PiTensorProduct.map (gMap K q)
      (CWMonom K q (⟨q+1, by omega⟩ : Fin (q+2))
        (⟨0, by omega⟩ : Fin (q+2))
        (⟨0, by omega⟩ : Fin (q+2))) = 0 := by
  rw [gMap_CWMonom]
  have hc : (Pi.single (⟨0, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K) ⟨q+1, by omega⟩ = 0 := by
    rw [Pi.single_apply]
    have : (⟨q+1, by omega⟩ : Fin (q+2)) ≠ ⟨0, by omega⟩ := by
      intro heq
      have := congrArg Fin.val heq
      simp at this
    simp
  rw [hc]; simp

end MMECWBlockAt002Sol

open MMECWBlockAt002Sol

theorem solution {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict
      (MMObj K 1 1 1)
      ((cwCanonicalGrading q (K := K)).blockSubtensor
        (fun i : Fin 3 =>
          match i with
          | ⟨0, _⟩ => 0
          | ⟨1, _⟩ => 0
          | ⟨2, _⟩ => 2)) := by
  refine ⟨MMECWBlockAt002Sol.toMM K q, ?_⟩
  show PiTensorProduct.map (MMECWBlockAt002Sol.toMM K q)
      ((cwCanonicalGrading q (K := K)).blockSubtensor MMECWBlockAt002Sol.σ_002).t =
      MMTensor K 1 1 1
  rw [map_toMM_block_eq_map_g]
  -- Generalize the omega-proofs to free metavariables to avoid pattern issues.
  set O : Fin (q+2) := ⟨0, by omega⟩ with hO
  set T : Fin (q+2) := ⟨q+1, by omega⟩ with hT
  -- Expand CWTensor and MMTensor.
  show PiTensorProduct.map (gMap K q)
      ((∑ i : Fin q,
          (CWMonom K q O
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2))
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) +
            CWMonom K q (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) O
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) +
            CWMonom K q (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2))
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) O)) +
        CWMonom K q O O T + CWMonom K q O T O + CWMonom K q T O O) = MMTensor K 1 1 1
  unfold MMTensor
  -- Now the expression uses `O` and `T` set-vars; metavariables for omega-proofs
  -- are unified at this level. Compute the LHS via linearity + per-monomial zeros.
  -- First, split the outer ((sum + OOT) + OTO) + TOO via map_add chain.
  set F := PiTensorProduct.map (gMap K q) with hF
  -- Define the "inner sum" and the three boundary terms with shared definitions
  -- to avoid omega-proof metavariable issues in the rewrite patterns.
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
  -- Now goal: F (innerSum + bOOT + bOTO + bTOO) = ...
  -- Use suffices to inject the rewritten form.
  suffices h : F innerSum + F bOOT + F bOTO + F bTOO = MMTensor K 1 1 1 by
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
  -- Now prove the simpler equation.
  -- Now LHS = F(∑) + F(OOT) + F(OTO) + F(TOO).
  -- Replace F(∑) with ∑ F(...).
  rw [show F innerSum = ∑ i : Fin q, F (CWMonom K q O
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2))
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) +
            CWMonom K q (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) O
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) +
            CWMonom K q (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2))
              (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) O) from by
      rw [hInnerSum]
      exact _root_.map_sum F _ Finset.univ]
  -- Replace each F(triple) with 0.
  have hF_triple : ∀ i : Fin q,
      F (CWMonom K q O
            (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2))
            (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) +
          CWMonom K q (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) O
            (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) +
          CWMonom K q (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2))
            (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) O) = 0 := by
    intro i
    set M : Fin (q+2) := ⟨(i : Fin q).val + 1, by omega⟩ with hM
    -- Goal: F (CWMonom K q O M M + CWMonom K q M O M + CWMonom K q M M O) = 0.
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
          (⟨(i : Fin q).val + 1, by omega⟩ : Fin (q+2)) O)) = 0 from by
      apply Finset.sum_eq_zero
      intros i _
      exact hF_triple i]
  -- Replace F(OTO) and F(TOO) with 0.
  rw [show F (CWMonom K q O T O) = 0 from by
      rw [show O = (⟨0, by omega⟩ : Fin (q+2)) from rfl]
      rw [show T = (⟨q+1, by omega⟩ : Fin (q+2)) from rfl]
      exact gMap_CWMonom_OTO K q]
  rw [show F (CWMonom K q T O O) = 0 from by
      rw [show O = (⟨0, by omega⟩ : Fin (q+2)) from rfl]
      rw [show T = (⟨q+1, by omega⟩ : Fin (q+2)) from rfl]
      exact gMap_CWMonom_TOO K q]
  -- Replace F(OOT) with the explicit pure tensor.
  rw [show F (CWMonom K q O O T) = (PiTensorProduct.tprod K) (fun s : Fin 3 =>
        match s with
        | ⟨0, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
        | ⟨1, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
        | ⟨2, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)) from by
      rw [show O = (⟨0, by omega⟩ : Fin (q+2)) from rfl]
      rw [show T = (⟨q+1, by omega⟩ : Fin (q+2)) from rfl]
      exact gMap_CWMonom_OOT K q]
  -- Clean up: 0 + tprod + 0 + 0 = tprod.
  simp only [zero_add, add_zero]
  -- Now: tprod K (...) = MMTensor K 1 1 1.
  -- Unfold MMTensor and collapse sums over Fin 1.
  unfold MMTensor
  rw [Fin.sum_univ_one, Fin.sum_univ_one, Fin.sum_univ_one]
  rfl
