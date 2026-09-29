-- Prove2me | solution 1 for mme_CW_value_ge_at_q6
-- status  : ACCEPTED   (disprove)
-- author  : @Community (Bot)
-- created : 2026-06-07T14:55:39.613247+00:00
-- url     : https://prove2.me/submissions/8ab5b1b1-8882-469e-814f-cb04a78be13a

import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_CW_support_pattern
import Definitions.Def_mme_tensor_type_grading
import Definitions.Def_mme_laser_pattern
import Mathlib.Algebra.Field.Rat

open MME

universe u

namespace MME.CWCanonicalAligned

variable {K : Type u} [Field K]

/-- The "type" of an index `k : Fin (q+2)`: `0` for the left boundary `0`,
`2` for the right boundary `q+1`, `1` for anything in between. -/
def typeOf (q : ℕ) (k : Fin (q+2)) : Fin 3 :=
  if k.val = 0 then 0
  else if k.val = q + 1 then 2
  else 1

/-- The `α`-th piece of the canonical 3-grading on `Fin (q+2) → K`: functions
supported on indices whose `typeOf` is `α`. We describe it as the span of the
indicator vectors `Pi.single k 1` for `k` with `typeOf q k = α`. -/
def gradePiece (K : Type u) [Field K] (q : ℕ) (α : Fin 3) :
    Submodule K (Fin (q+2) → K) :=
  Submodule.span K (Set.range (fun k : {k : Fin (q+2) // typeOf q k = α} =>
    (Pi.single (k : Fin (q+2)) (1 : K) : Fin (q+2) → K)))

/-- A characterization: `f ∈ gradePiece K q α` iff `f` is zero outside `typeOf⁻¹(α)`. -/
lemma mem_gradePiece_iff (q : ℕ) (α : Fin 3) (f : Fin (q+2) → K) :
    f ∈ gradePiece K q α ↔ ∀ k : Fin (q+2), typeOf q k ≠ α → f k = 0 := by
  classical
  constructor
  · intro hf
    refine Submodule.span_induction (p := fun g _ => ∀ k, typeOf q k ≠ α → g k = 0)
      ?_ ?_ ?_ ?_ hf
    · rintro g ⟨k, rfl⟩ j hj
      by_cases hjk : j = (k : Fin (q+2))
      · subst hjk; exact absurd k.2 hj
      · simp [Pi.single_apply, if_neg hjk]
    · intro k _; rfl
    · intro x y _ _ hx hy k hk
      simp [hx k hk, hy k hk]
    · intro c x _ hx k hk
      simp [hx k hk]
  · intro h
    -- f = ∑ k : Fin (q+2) with typeOf k = α, f k • Pi.single k 1
    have hsum :
        f = ∑ k ∈ (Finset.univ.filter (fun k : Fin (q+2) => typeOf q k = α)),
                f k • (Pi.single k (1 : K) : Fin (q+2) → K) := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hj : typeOf q j = α
      · rw [Finset.sum_eq_single j]
        · simp
        · intro k _ hk
          have : (Pi.single k (1 : K) : Fin (q+2) → K) j = 0 := by
            simp [Pi.single_apply, if_neg (Ne.symm hk)]
          rw [this]; ring
        · intro hjmem
          exfalso; apply hjmem
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
      · symm
        rw [h j hj]
        apply Finset.sum_eq_zero
        intro k hk
        rw [Finset.mem_filter] at hk
        have hkj : j ≠ k := by
          intro heq
          rw [heq] at hj
          exact hj hk.2
        have : (Pi.single k (1 : K) : Fin (q+2) → K) j = 0 := by
          simp [Pi.single_apply, if_neg hkj]
        rw [this]; ring
    rw [hsum]
    apply Submodule.sum_mem
    intro k hk
    rw [Finset.mem_filter] at hk
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨⟨k, hk.2⟩, rfl⟩

/-- Pi.single at index `k` is in the `typeOf q k`-th grade piece. -/
lemma single_mem_gradePiece (q : ℕ) (k : Fin (q+2)) :
    (Pi.single k 1 : Fin (q+2) → K) ∈ gradePiece K q (typeOf q k) := by
  apply Submodule.subset_span
  exact ⟨⟨k, rfl⟩, rfl⟩

/-- The standard piece-projection: zero out `f` outside `typeOf⁻¹(α)`. -/
def project (q : ℕ) (α : Fin 3) (f : Fin (q+2) → K) : Fin (q+2) → K :=
  fun k => if typeOf q k = α then f k else 0

lemma project_mem (q : ℕ) (α : Fin 3) (f : Fin (q+2) → K) :
    project q α f ∈ gradePiece K q α := by
  rw [mem_gradePiece_iff]
  intro k hk
  simp [project, hk]

lemma sum_project (q : ℕ) (f : Fin (q+2) → K) :
    (∑ α : Fin 3, project q α f) = f := by
  funext k
  simp only [Finset.sum_apply, project]
  -- typeOf q k is some specific α₀ ∈ Fin 3; exactly that term contributes f k, others 0.
  have : ∑ α : Fin 3, (if typeOf q k = α then f k else 0) = f k := by
    rw [Finset.sum_eq_single (typeOf q k)]
    · simp
    · intros α _ hα
      rw [if_neg (Ne.symm hα)]
    · intro h; exact absurd (Finset.mem_univ _) h
  exact this

/-- The grading is internal: each mode space `Fin (q+2) → K` is the internal direct
sum of `gradePiece K q 0`, `gradePiece K q 1`, `gradePiece K q 2`. -/
lemma isInternal_gradePiece (q : ℕ) :
    DirectSum.IsInternal (fun α : Fin 3 => gradePiece K q α) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · -- iSupIndep
    rw [iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero]
    intro s v hv hsum α hα
    -- v α is in gradePiece, supported on typeOf⁻¹(α).
    have hvα : ∀ k, typeOf q k ≠ α → v α k = 0 :=
      (mem_gradePiece_iff q α (v α)).mp (hv α hα)
    -- For each k, ∑ β ∈ s, v β k = 0
    funext k
    have hk_sum : (∑ β ∈ s, v β) k = 0 := by rw [hsum]; rfl
    rw [Finset.sum_apply] at hk_sum
    -- Only the β with typeOf q k = β can be nonzero at k.
    -- We need to show v α k = 0.
    by_cases hk : typeOf q k = α
    · -- The β = α term is v α k. For other β ∈ s with β ≠ α and v β ∈ gradePiece β:
      -- v β k = 0 because typeOf q k = α ≠ β.
      have hall : ∀ β ∈ s, β ≠ α → v β k = 0 := by
        intro β hβ hβne
        have hvβ : ∀ j, typeOf q j ≠ β → v β j = 0 :=
          (mem_gradePiece_iff q β (v β)).mp (hv β hβ)
        apply hvβ
        rw [hk]; exact hβne.symm
      -- So ∑ β ∈ s, v β k = v α k + ∑ β ∈ s \ {α}, v β k = v α k + 0 = v α k.
      rw [← Finset.add_sum_erase s _ hα] at hk_sum
      have hzero : (∑ β ∈ s.erase α, v β k) = 0 := by
        apply Finset.sum_eq_zero
        intro β hβ
        rw [Finset.mem_erase] at hβ
        exact hall β hβ.2 hβ.1
      rw [hzero, add_zero] at hk_sum
      exact hk_sum
    · -- v α k = 0 by the support hypothesis directly.
      exact hvα k hk
  · -- iSup = ⊤
    rw [eq_top_iff]
    intro f _
    -- f = ∑ α, project α f, and each project α f ∈ gradePiece α ≤ iSup
    rw [← sum_project q f]
    apply Submodule.sum_mem
    intro α _
    exact Submodule.mem_iSup_of_mem α (project_mem q α f)

/-- The canonical 3-grading on `CWObj K q`. All three modes are `Fin (q+2) → K`,
so we use `gradePiece` in each mode. -/
noncomputable def canonicalGrading (q : ℕ) : (CWObj K q).TypeGrading 3 where
  decomp := fun i α =>
    -- (CWObj K q).V i = CWSpace K q i. By definition it's Fin (q+2) → K for each i.
    -- We need to give a Submodule K ((CWObj K q).V i). Match on i.
    match i with
    | ⟨0, _⟩ => gradePiece K q α
    | ⟨1, _⟩ => gradePiece K q α
    | ⟨2, _⟩ => gradePiece K q α
  is_internal := fun i => by
    match i with
    | ⟨0, _⟩ => exact isInternal_gradePiece q
    | ⟨1, _⟩ => exact isInternal_gradePiece q
    | ⟨2, _⟩ => exact isInternal_gradePiece q

/-- `typeOf q 0 = 0`. -/
@[simp] lemma typeOf_zero (q : ℕ) :
    typeOf q (⟨0, by omega⟩ : Fin (q+2)) = 0 := by
  simp [typeOf]

/-- `typeOf q (q+1) = 2`. -/
@[simp] lemma typeOf_qPlusOne (q : ℕ) :
    typeOf q (⟨q+1, by omega⟩ : Fin (q+2)) = 2 := by
  simp [typeOf]

/-- For `i : Fin q`, `typeOf q ⟨i.val + 1, _⟩ = 1`. -/
@[simp] lemma typeOf_middle (q : ℕ) (i : Fin q) :
    typeOf q (⟨i.val + 1, by omega⟩ : Fin (q+2)) = 1 := by
  simp [typeOf]
  intro h
  omega

end MME.CWCanonicalAligned

namespace MME.CWCanonicalAligned

/-! ## Witness construction for the LaserAlignedSupport

We index the `3q + 3` rank-one terms of `CWTensor K q` by the sum type
`(Fin q × Fin 3) ⊕ Fin 3`, where the first component picks one of the three
"middle" terms for each `i : Fin q`, and the second picks one of the three
"boundary" terms. The standard equivalence `(Fin q × Fin 3) ⊕ Fin 3 ≃ Fin (3*q + 3)`
converts this to the `Fin k` shape expected by `LaserAlignedSupport`. -/

variable (K : Type u) [Field K]

/-- Factor function for a triple of indices `(a, b, c)`: the rank-one tensor
`e_a ⊗ e_b ⊗ e_c` as a function `Fin 3 → CWSpace K q i`. -/
def factorFun (q : ℕ) (a b c : Fin (q+2)) :
    ∀ i : Fin 3, CWSpace K q i :=
  fun i =>
    match i with
    | ⟨0, _⟩ => (Pi.single a (1 : K) : Fin (q+2) → K)
    | ⟨1, _⟩ => (Pi.single b (1 : K) : Fin (q+2) → K)
    | ⟨2, _⟩ => (Pi.single c (1 : K) : Fin (q+2) → K)

/-- A factor function for the rank-one term, in the form expected by `tprod K (f j)`. -/
def fSum (q : ℕ) : (Fin q × Fin 3) ⊕ Fin 3 → ∀ i : Fin 3, CWSpace K q i :=
  fun s =>
    let O : Fin (q+2) := ⟨0, by omega⟩
    let T : Fin (q+2) := ⟨q+1, by omega⟩
    match s with
    | Sum.inl (i, r) =>
      let M : Fin (q+2) := ⟨i.val + 1, by omega⟩
      match r with
      | ⟨0, _⟩ => factorFun K q O M M
      | ⟨1, _⟩ => factorFun K q M O M
      | ⟨2, _⟩ => factorFun K q M M O
    | Sum.inr r =>
      match r with
      | ⟨0, _⟩ => factorFun K q O O T
      | ⟨1, _⟩ => factorFun K q O T O
      | ⟨2, _⟩ => factorFun K q T O O

/-- Type-triple of each indexed rank-one term. -/
def τSum (q : ℕ) : (Fin q × Fin 3) ⊕ Fin 3 → Fin 3 × Fin 3 × Fin 3 :=
  fun s => match s with
    | Sum.inl (_, r) =>
      match r with
      | ⟨0, _⟩ => (0, 1, 1)
      | ⟨1, _⟩ => (1, 0, 1)
      | ⟨2, _⟩ => (1, 1, 0)
    | Sum.inr r =>
      match r with
      | ⟨0, _⟩ => (0, 0, 2)
      | ⟨1, _⟩ => (0, 2, 0)
      | ⟨2, _⟩ => (2, 0, 0)

variable {K}

/-- The factor function `fSum` produces tensor products matching the CWMonom monomials. -/
lemma tprod_fSum (q : ℕ) (s : (Fin q × Fin 3) ⊕ Fin 3) :
    PiTensorProduct.tprod K (fSum K q s) =
      (match s with
       | Sum.inl (i, r) =>
         let O : Fin (q+2) := ⟨0, by omega⟩
         let M : Fin (q+2) := ⟨i.val + 1, by omega⟩
         match r with
         | ⟨0, _⟩ => CWMonom K q O M M
         | ⟨1, _⟩ => CWMonom K q M O M
         | ⟨2, _⟩ => CWMonom K q M M O
       | Sum.inr r =>
         let O : Fin (q+2) := ⟨0, by omega⟩
         let T : Fin (q+2) := ⟨q+1, by omega⟩
         match r with
         | ⟨0, _⟩ => CWMonom K q O O T
         | ⟨1, _⟩ => CWMonom K q O T O
         | ⟨2, _⟩ => CWMonom K q T O O) := by
  rcases s with ⟨i, r⟩ | r
  · match r with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
  · match r with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl

/-- Sum of all rank-one terms equals `CWTensor K q`. -/
lemma sum_tprod_fSum_eq (q : ℕ) :
    (∑ s : (Fin q × Fin 3) ⊕ Fin 3, PiTensorProduct.tprod K (fSum K q s)) =
      CWTensor K q := by
  -- Split the sum over the disjoint union.
  rw [Fintype.sum_sum_type]
  -- The Sum.inl part is ∑ (i, r) : Fin q × Fin 3, tprod K (fSum K q (.inl (i,r)))
  --                    = ∑ i, ∑ r, ... = ∑ i, (term_0 + term_1 + term_2)
  -- The Sum.inr part is the three boundary terms.
  -- Let's compute each.
  have hL : (∑ p : Fin q × Fin 3, PiTensorProduct.tprod K (fSum K q (Sum.inl p))) =
      ∑ i : Fin q,
        let M : Fin (q+2) := ⟨i.val + 1, by omega⟩
        let O : Fin (q+2) := ⟨0, by omega⟩
        CWMonom K q O M M + CWMonom K q M O M + CWMonom K q M M O := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    -- Sum over r : Fin 3
    rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton]
    -- Now we need to show that the three terms match.
    show PiTensorProduct.tprod K (fSum K q (Sum.inl (i, 0))) +
         (PiTensorProduct.tprod K (fSum K q (Sum.inl (i, 1))) +
          PiTensorProduct.tprod K (fSum K q (Sum.inl (i, 2)))) =
      let M : Fin (q+2) := ⟨i.val + 1, by omega⟩
      let O : Fin (q+2) := ⟨0, by omega⟩
      CWMonom K q O M M + CWMonom K q M O M + CWMonom K q M M O
    simp only [tprod_fSum]
    show CWMonom K q _ _ _ + (CWMonom K q _ _ _ + CWMonom K q _ _ _)
       = CWMonom K q _ _ _ + CWMonom K q _ _ _ + CWMonom K q _ _ _
    abel
  have hR : (∑ r : Fin 3, PiTensorProduct.tprod K (fSum K q (Sum.inr r))) =
      let O : Fin (q+2) := ⟨0, by omega⟩
      let T : Fin (q+2) := ⟨q+1, by omega⟩
      CWMonom K q O O T + CWMonom K q O T O + CWMonom K q T O O := by
    rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton]
    simp only [tprod_fSum]
    show CWMonom K q _ _ _ + (CWMonom K q _ _ _ + CWMonom K q _ _ _) =
         CWMonom K q _ _ _ + CWMonom K q _ _ _ + CWMonom K q _ _ _
    abel
  rw [hL, hR]
  -- Now the goal is: (∑ i, three middle terms) + (three boundary terms) = CWTensor K q
  -- Unfold CWTensor K q
  unfold CWTensor
  -- The boundary parts match termwise; the middle sums also match (only associativity differs).
  simp only [add_assoc]

end MME.CWCanonicalAligned

/-- **The CW tensor admits the canonical 3-grading with laser-aligned support.** -/
theorem mme_CW_canonical_aligned_witness {K : Type u} [Field K] (q : ℕ) :
    ∃ G : (CWObj K q).TypeGrading 3,
      TensorObj.LaserAlignedSupport G CWSupportPattern := by
  classical
  refine ⟨MME.CWCanonicalAligned.canonicalGrading q, ?_⟩
  -- Set up the equivalence between Fin (q*3 + 3) and (Fin q × Fin 3) ⊕ Fin 3.
  -- Use Fintype.sum_equiv to rewrite the goal in terms of the sum type.
  let σ : (Fin q × Fin 3) ⊕ Fin 3 ≃ Fin (q * 3 + 3) :=
    (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv
  let k := q * 3 + 3
  let f : Fin k → ∀ i : Fin 3, (CWObj K q).V i :=
    fun j => MME.CWCanonicalAligned.fSum K q (σ.symm j)
  let τ : Fin k → Fin 3 × Fin 3 × Fin 3 :=
    fun j => MME.CWCanonicalAligned.τSum q (σ.symm j)
  refine ⟨k, f, τ, ?_, ?_⟩
  · -- (CWObj K q).t = ∑ j, tprod K (f j)
    show CWTensor K q = ∑ j, PiTensorProduct.tprod K (f j)
    rw [← MME.CWCanonicalAligned.sum_tprod_fSum_eq q]
    -- ∑ s : Sum, tprod K (fSum s) = ∑ j : Fin k, tprod K (fSum (σ.symm j))
    -- Use Fintype.sum_equiv σ.
    exact (Fintype.sum_equiv σ.symm _ _ (fun _ => rfl)).symm
  · -- For each j, τ j ∈ S and f j i ∈ classOf …
    intro j
    -- Helper lemmas: membership of Pi.single at types 0, 1, 2.
    have hO : ∀ (α : Fin 3),
        MME.CWCanonicalAligned.typeOf q (⟨0, by omega⟩ : Fin (q+2)) = α →
        (Pi.single (⟨0, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K) ∈
          MME.CWCanonicalAligned.gradePiece K q α := by
      intro α hα
      have := MME.CWCanonicalAligned.single_mem_gradePiece (K := K) q
          (⟨0, by omega⟩ : Fin (q+2))
      rw [hα] at this; exact this
    have hT : ∀ (α : Fin 3),
        MME.CWCanonicalAligned.typeOf q (⟨q+1, by omega⟩ : Fin (q+2)) = α →
        (Pi.single (⟨q+1, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K) ∈
          MME.CWCanonicalAligned.gradePiece K q α := by
      intro α hα
      have := MME.CWCanonicalAligned.single_mem_gradePiece (K := K) q
          (⟨q+1, by omega⟩ : Fin (q+2))
      rw [hα] at this; exact this
    have hM : ∀ (i : Fin q) (α : Fin 3),
        MME.CWCanonicalAligned.typeOf q (⟨i.val+1, by omega⟩ : Fin (q+2)) = α →
        (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K) ∈
          MME.CWCanonicalAligned.gradePiece K q α := by
      intro i α hα
      have := MME.CWCanonicalAligned.single_mem_gradePiece (K := K) q
          (⟨i.val+1, by omega⟩ : Fin (q+2))
      rw [hα] at this; exact this
    -- Now case analysis on the witness index.
    -- Rewrite f, τ to their fSum/τSum definitions evaluated at σ.symm j.
    show MME.CWCanonicalAligned.τSum q (σ.symm j) ∈ CWSupportPattern ∧ _
    -- Generalize over σ.symm j.
    revert j
    suffices ∀ s : (Fin q × Fin 3) ⊕ Fin 3,
        MME.CWCanonicalAligned.τSum q s ∈ CWSupportPattern ∧
        MME.CWCanonicalAligned.fSum K q s 0 ∈
          (MME.CWCanonicalAligned.canonicalGrading q).classOf 0
            (MME.CWCanonicalAligned.τSum q s).1 ∧
        MME.CWCanonicalAligned.fSum K q s 1 ∈
          (MME.CWCanonicalAligned.canonicalGrading q).classOf 1
            (MME.CWCanonicalAligned.τSum q s).2.1 ∧
        MME.CWCanonicalAligned.fSum K q s 2 ∈
          (MME.CWCanonicalAligned.canonicalGrading q).classOf 2
            (MME.CWCanonicalAligned.τSum q s).2.2 by
      intro j
      exact this (σ.symm j)
    intro s
    rcases s with ⟨i, r⟩ | r
    · -- Middle case
      match r with
      | ⟨0, _⟩ =>
        refine ⟨?_, ?_, ?_, ?_⟩
        · show ((0, 1, 1) : Fin 3 × Fin 3 × Fin 3) ∈ CWSupportPattern; decide
        · exact hO 0 (MME.CWCanonicalAligned.typeOf_zero q)
        · exact hM i 1 (MME.CWCanonicalAligned.typeOf_middle q i)
        · exact hM i 1 (MME.CWCanonicalAligned.typeOf_middle q i)
      | ⟨1, _⟩ =>
        refine ⟨?_, ?_, ?_, ?_⟩
        · show ((1, 0, 1) : Fin 3 × Fin 3 × Fin 3) ∈ CWSupportPattern; decide
        · exact hM i 1 (MME.CWCanonicalAligned.typeOf_middle q i)
        · exact hO 0 (MME.CWCanonicalAligned.typeOf_zero q)
        · exact hM i 1 (MME.CWCanonicalAligned.typeOf_middle q i)
      | ⟨2, _⟩ =>
        refine ⟨?_, ?_, ?_, ?_⟩
        · show ((1, 1, 0) : Fin 3 × Fin 3 × Fin 3) ∈ CWSupportPattern; decide
        · exact hM i 1 (MME.CWCanonicalAligned.typeOf_middle q i)
        · exact hM i 1 (MME.CWCanonicalAligned.typeOf_middle q i)
        · exact hO 0 (MME.CWCanonicalAligned.typeOf_zero q)
    · -- Boundary case
      match r with
      | ⟨0, _⟩ =>
        refine ⟨?_, ?_, ?_, ?_⟩
        · show ((0, 0, 2) : Fin 3 × Fin 3 × Fin 3) ∈ CWSupportPattern; decide
        · exact hO 0 (MME.CWCanonicalAligned.typeOf_zero q)
        · exact hO 0 (MME.CWCanonicalAligned.typeOf_zero q)
        · exact hT 2 (MME.CWCanonicalAligned.typeOf_qPlusOne q)
      | ⟨1, _⟩ =>
        refine ⟨?_, ?_, ?_, ?_⟩
        · show ((0, 2, 0) : Fin 3 × Fin 3 × Fin 3) ∈ CWSupportPattern; decide
        · exact hO 0 (MME.CWCanonicalAligned.typeOf_zero q)
        · exact hT 2 (MME.CWCanonicalAligned.typeOf_qPlusOne q)
        · exact hO 0 (MME.CWCanonicalAligned.typeOf_zero q)
      | ⟨2, _⟩ =>
        refine ⟨?_, ?_, ?_, ?_⟩
        · show ((2, 0, 0) : Fin 3 × Fin 3 × Fin 3) ∈ CWSupportPattern; decide
        · exact hT 2 (MME.CWCanonicalAligned.typeOf_qPlusOne q)
        · exact hO 0 (MME.CWCanonicalAligned.typeOf_zero q)
        · exact hO 0 (MME.CWCanonicalAligned.typeOf_zero q)

/-- Disproof of the placeholder-value branch. The current platform definition
has `laserValueFormula = 1`, so the claimed `5/2` lower bound is false for the
canonical aligned CW grading. -/
theorem solution :
    ¬ (∀ {K : Type} [Field K] (G : (CWObj K 6).TypeGrading 3),
        TensorObj.LaserAlignedSupport G CWSupportPattern →
        (5 : ℝ) / 2 ≤ laserValueFormula G CWSupportPattern) := by
  intro h
  obtain ⟨G, hAlign⟩ := mme_CW_canonical_aligned_witness (K := ℚ) 6
  have hbad : (5 : ℝ) / 2 ≤ laserValueFormula G CWSupportPattern :=
    h (K := ℚ) G hAlign
  change (5 : ℝ) / 2 ≤ (1 : ℝ) at hbad
  norm_num at hbad
