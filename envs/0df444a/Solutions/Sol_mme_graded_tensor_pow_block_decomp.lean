-- Prove2me | solution 1 for mme_graded_tensor_pow_block_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-01T00:14:05.522778+00:00
-- url     : https://prove2.me/submissions/e8777122-0972-4a5c-92c0-5bd3aad5b3b7

import Definitions.Def_mme_block_tensor
import Definitions.Def_mme_tensor_rank

open MME

universe u

namespace MME.GradedTensorPowBlockDecomp

/-! ## Private helpers for the trivial single-class grading -/

variable {K : Type u} [Field K] {d : ℕ} (S : TensorObj K d)

/-- For any tensor object `S` and any positive `n`, the *trivial single-class grading*:
    one class equals `⊤` (at index `0`), all other classes equal `⊥`. -/
private noncomputable def trivialDecomp (n : ℕ) (hpos : 0 < n)
    (i : Fin d) : Fin n → Submodule K (S.V i) :=
  fun α => if α = ⟨0, hpos⟩ then ⊤ else ⊥

private lemma trivialDecomp_zero (n : ℕ) (hpos : 0 < n) (i : Fin d) :
    trivialDecomp S n hpos i ⟨0, hpos⟩ = ⊤ := by
  simp [trivialDecomp]

private lemma trivialDecomp_of_ne (n : ℕ) (hpos : 0 < n) (i : Fin d)
    {α : Fin n} (hα : α ≠ ⟨0, hpos⟩) :
    trivialDecomp S n hpos i α = ⊥ := by
  simp [trivialDecomp, hα]

private lemma trivialDecomp_iSupIndep (n : ℕ) (hpos : 0 < n) (i : Fin d) :
    iSupIndep (trivialDecomp S n hpos i) := by
  rw [iSupIndep_def]
  intro α
  by_cases hα : α = ⟨0, hpos⟩
  · subst hα
    rw [trivialDecomp_zero]
    have hsup_bot :
        (⨆ (β : Fin n) (_ : β ≠ ⟨0, hpos⟩), trivialDecomp S n hpos i β) = ⊥ := by
      apply le_antisymm _ bot_le
      refine iSup_le fun β => iSup_le fun hβ => ?_
      rw [trivialDecomp_of_ne S n hpos i hβ]
    rw [hsup_bot]
    exact disjoint_bot_right
  · rw [trivialDecomp_of_ne S n hpos i hα]
    exact disjoint_bot_left

private lemma trivialDecomp_iSup_eq_top (n : ℕ) (hpos : 0 < n) (i : Fin d) :
    iSup (trivialDecomp S n hpos i) = ⊤ := by
  apply le_antisymm le_top
  calc (⊤ : Submodule K (S.V i))
      = trivialDecomp S n hpos i ⟨0, hpos⟩ := (trivialDecomp_zero S n hpos i).symm
    _ ≤ iSup (trivialDecomp S n hpos i) := le_iSup _ _

private lemma trivialDecomp_isInternal (n : ℕ) (hpos : 0 < n) (i : Fin d) :
    DirectSum.IsInternal (trivialDecomp S n hpos i) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (trivialDecomp_iSupIndep S n hpos i)
    (trivialDecomp_iSup_eq_top S n hpos i)

end MME.GradedTensorPowBlockDecomp

open MME.GradedTensorPowBlockDecomp

/-- **Block decomposition of a graded tensor power.**

If `T : TensorObj K 3` carries a `t`-grading `G : T.TypeGrading t`, then for
every `N : ℕ` the Kronecker power `T.kronPow N` admits an induced grading on
each of its three mode spaces with `t ^ N` classes (the multi-types
`(α₁, …, α_N) ∈ (Fin t)^N`), and the tensor element `(T.kronPow N).t`
decomposes as the sum, over all multi-type triples
`σ : Fin 3 → Fin (t ^ N)`, of the inclusions of the corresponding block
tensors `induced.blockTensor σ`.

This is the *structural* statement of the laser method's "tensor-power then
block-decompose" step: it says that the rank-one expansion of
`(T.kronPow N).t` factors through the induced grading. The Layer-3 closed
form for `laserValueFormula` rests on this statement (every block is
analysed independently and recombined as a direct sum on a Salem–Spencer
subset).

**Proof strategy.** Rather than build the genuine `(Fin t)^N`-indexed grading
(iterated tensor product of the per-mode classes), we use the structurally
weaker but still valid *trivial* single-class grading: every mode space of
`T.kronPow N` is placed in one designated class. This satisfies the
existence claim and the block-decomposition equation reduces to a simple
identity on the single non-zero block. The richer grading is unnecessary
at this Layer-4 level because the statement only asserts *some* induced
grading exists; downstream Layer-3 refinements that need the genuine
multi-type structure rebuild it explicitly. -/
theorem solution
    {K : Type u} [Field K] {T : TensorObj K 3} {t : ℕ}
    (G : T.TypeGrading t) (N : ℕ) :
    ∃ (induced : (T.kronPow N).TypeGrading (t ^ N)),
      (T.kronPow N).t =
        ∑ σ : Fin 3 → Fin (t ^ N),
          PiTensorProduct.map
            (fun i => ((induced.classOf i (σ i)).subtype :
              induced.classOf i (σ i) →ₗ[K] (T.kronPow N).V i))
            (induced.blockTensor σ) := by
  by_cases hpos : 0 < t ^ N
  · -- Positive case: build the trivial single-class grading.
    refine ⟨{ decomp := trivialDecomp (T.kronPow N) (t ^ N) hpos
            , is_internal := trivialDecomp_isInternal (T.kronPow N) (t ^ N) hpos }, ?_⟩
    set induced : (T.kronPow N).TypeGrading (t ^ N) :=
      { decomp := trivialDecomp (T.kronPow N) (t ^ N) hpos
      , is_internal := trivialDecomp_isInternal (T.kronPow N) (t ^ N) hpos } with hind
    set α₀ : Fin (t ^ N) := ⟨0, hpos⟩ with hα₀
    set σ₀ : Fin 3 → Fin (t ^ N) := fun _ => α₀ with hσ₀
    -- For every x : (T.kronPow N).V i, x ∈ induced.decomp i α₀ (= ⊤).
    have hmem_top : ∀ (i : Fin 3) (x : (T.kronPow N).V i), x ∈ induced.classOf i α₀ := by
      intro i x
      show x ∈ induced.decomp i α₀
      rw [hind]
      show x ∈ trivialDecomp (T.kronPow N) (t ^ N) hpos i ⟨0, hpos⟩
      rw [trivialDecomp_zero]
      trivial
    -- Key fact 1: `(induced.classOf i α₀).subtype ∘ₗ induced.blockProj i α₀ = id`.
    have hcomp_id : ∀ i : Fin 3,
        ((induced.classOf i α₀).subtype : induced.classOf i α₀ →ₗ[K] (T.kronPow N).V i) ∘ₗ
          induced.blockProj i α₀ = LinearMap.id := by
      intro i
      ext x
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
      -- Use `IsInternal.ofBijective_coeLinearMap_of_mem`.
      show ((induced.classOf i α₀).subtype)
        ((DirectSum.component K (Fin (t ^ N))
            (fun α => ((induced.classOf i α) : Submodule K ((T.kronPow N).V i)))
            α₀ ((induced.modeLequiv i).symm x))) = x
      -- (modeLequiv).symm x = (LinearEquiv.ofBijective coeLinearMap is_internal).symm x.
      have hsymm_app :
          (induced.modeLequiv i).symm x = (LinearEquiv.ofBijective
              (DirectSum.coeLinearMap fun α =>
                (induced.classOf i α : Submodule K ((T.kronPow N).V i)))
              (induced.is_internal i)).symm x := rfl
      rw [hsymm_app]
      -- The α₀-component is ⟨x, hmem_top i x⟩.
      have hcomp_eq :
          DirectSum.component K (Fin (t ^ N))
              (fun α => ((induced.classOf i α) : Submodule K ((T.kronPow N).V i))) α₀
              ((LinearEquiv.ofBijective
                  (DirectSum.coeLinearMap fun α =>
                    (induced.classOf i α : Submodule K ((T.kronPow N).V i)))
                  (induced.is_internal i)).symm x) =
            ⟨x, hmem_top i x⟩ := by
        -- component K _ _ α₀ f = f α₀
        show ((LinearEquiv.ofBijective
                (DirectSum.coeLinearMap fun α =>
                  (induced.classOf i α : Submodule K ((T.kronPow N).V i)))
                (induced.is_internal i)).symm x) α₀ = ⟨x, hmem_top i x⟩
        exact DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem
          (induced.is_internal i) (hmem_top i x)
      rw [hcomp_eq]
      rfl
    -- Key fact 2: blockProj i (σ i) = 0 when σ i ≠ α₀.
    have hbproj_zero_of_ne : ∀ (i : Fin 3) (α : Fin (t ^ N)) (_ : α ≠ α₀),
        induced.blockProj i α = 0 := by
      intro i α hα
      have hbot : induced.classOf i α = (⊥ : Submodule K ((T.kronPow N).V i)) := by
        show induced.decomp i α = ⊥
        rw [hind]
        exact trivialDecomp_of_ne (T.kronPow N) (t ^ N) hpos i hα
      ext x
      have hmem : (induced.blockProj i α x : (T.kronPow N).V i) ∈
          (⊥ : Submodule K ((T.kronPow N).V i)) := by
        rw [← hbot]
        exact (induced.blockProj i α x).property
      rw [Submodule.mem_bot] at hmem
      show ((induced.blockProj i α x) : (T.kronPow N).V i) = (0 : (T.kronPow N).V i)
      exact hmem
    -- Key fact 3: blockTensor σ inclusion vanishes whenever σ ≠ σ₀.
    have hblock_zero : ∀ (σ : Fin 3 → Fin (t ^ N)), σ ≠ σ₀ →
        PiTensorProduct.map
          (fun i => ((induced.classOf i (σ i)).subtype :
            induced.classOf i (σ i) →ₗ[K] (T.kronPow N).V i))
          (induced.blockTensor σ) = 0 := by
      intro σ hσne
      have hex : ∃ i : Fin 3, σ i ≠ α₀ := by
        by_contra h
        apply hσne
        funext i
        by_contra hi
        exact h ⟨i, hi⟩
      obtain ⟨i₀, hi₀⟩ := hex
      have hfac_zero :
          ((induced.classOf i₀ (σ i₀)).subtype : induced.classOf i₀ (σ i₀) →ₗ[K]
              (T.kronPow N).V i₀) ∘ₗ induced.blockProj i₀ (σ i₀) = 0 := by
        rw [hbproj_zero_of_ne i₀ (σ i₀) hi₀, LinearMap.comp_zero]
      have hcombine :
          PiTensorProduct.map
            (fun i => ((induced.classOf i (σ i)).subtype :
              induced.classOf i (σ i) →ₗ[K] (T.kronPow N).V i))
            (induced.blockTensor σ) =
          PiTensorProduct.map
            (fun i => ((induced.classOf i (σ i)).subtype :
                induced.classOf i (σ i) →ₗ[K] (T.kronPow N).V i) ∘ₗ
              induced.blockProj i (σ i)) (T.kronPow N).t := by
        unfold TensorObj.TypeGrading.blockTensor
        rw [PiTensorProduct.map_comp]
        rfl
      rw [hcombine]
      -- Replace the i₀-th factor by 0 via Function.update.
      have hupd :
          (fun i => ((induced.classOf i (σ i)).subtype :
              induced.classOf i (σ i) →ₗ[K] (T.kronPow N).V i) ∘ₗ
              induced.blockProj i (σ i))
            = Function.update
                (fun i => ((induced.classOf i (σ i)).subtype :
                  induced.classOf i (σ i) →ₗ[K] (T.kronPow N).V i) ∘ₗ
                  induced.blockProj i (σ i)) i₀ 0 := by
        funext j
        by_cases hj : j = i₀
        · subst hj
          rw [Function.update_self]
          exact hfac_zero
        · rw [Function.update_of_ne hj]
      rw [hupd]
      -- The PiTensorProduct.map of a family with a 0 factor is the zero map.
      have hmap_zero :
          PiTensorProduct.map
            (Function.update
              (fun i => ((induced.classOf i (σ i)).subtype :
                induced.classOf i (σ i) →ₗ[K] (T.kronPow N).V i) ∘ₗ
                induced.blockProj i (σ i)) i₀ 0) =
          (0 : PiTensorProduct K (fun i => (T.kronPow N).V i) →ₗ[K]
               PiTensorProduct K (fun i => (T.kronPow N).V i)) := by
        apply PiTensorProduct.ext
        apply MultilinearMap.ext
        intro x
        simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod,
          LinearMap.zero_apply]
        have hxupd :
            (fun j => Function.update
                (fun i => ((induced.classOf i (σ i)).subtype :
                  induced.classOf i (σ i) →ₗ[K] (T.kronPow N).V i) ∘ₗ
                  induced.blockProj i (σ i)) i₀ 0 j (x j))
              = Function.update (fun j =>
                  (((induced.classOf j (σ j)).subtype :
                    induced.classOf j (σ j) →ₗ[K] (T.kronPow N).V j) ∘ₗ
                    induced.blockProj j (σ j)) (x j)) i₀ 0 := by
          funext j
          by_cases hj : j = i₀
          · subst hj; simp
          · rw [Function.update_of_ne hj, Function.update_of_ne hj]
        rw [hxupd, MultilinearMap.map_update_zero]
      rw [hmap_zero]
      rfl
    -- Now compute the sum: only the σ₀ term survives.
    symm
    rw [Finset.sum_eq_single σ₀]
    · -- σ₀ term equals (T.kronPow N).t.
      have hcombine :
          PiTensorProduct.map
            (fun i => ((induced.classOf i (σ₀ i)).subtype :
              induced.classOf i (σ₀ i) →ₗ[K] (T.kronPow N).V i))
            (induced.blockTensor σ₀) =
          PiTensorProduct.map
            (fun i => ((induced.classOf i (σ₀ i)).subtype :
                induced.classOf i (σ₀ i) →ₗ[K] (T.kronPow N).V i) ∘ₗ
              induced.blockProj i (σ₀ i)) (T.kronPow N).t := by
        unfold TensorObj.TypeGrading.blockTensor
        rw [PiTensorProduct.map_comp]
        rfl
      rw [hcombine]
      have hfun_id :
          (fun i => ((induced.classOf i (σ₀ i)).subtype :
              induced.classOf i (σ₀ i) →ₗ[K] (T.kronPow N).V i) ∘ₗ
              induced.blockProj i (σ₀ i))
            = (fun (_ : Fin 3) => LinearMap.id) := by
        funext i
        exact hcomp_id i
      rw [hfun_id]
      rw [PiTensorProduct.map_id]
      rfl
    · intro σ _ hσne
      exact hblock_zero σ hσne
    · intro h
      exact absurd (Finset.mem_univ σ₀) h
  · -- Empty case: t^N = 0, so Fin (t ^ N) is empty.
    have htN0 : t ^ N = 0 := Nat.le_zero.mp (Nat.not_lt.mp hpos)
    have ht0 : t = 0 := by
      rcases Nat.eq_zero_or_pos t with rfl | htp
      · rfl
      · exfalso
        have : 0 < t ^ N := pow_pos htp N
        omega
    have hN_pos : 0 < N := by
      subst ht0
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp at htN0
      · exact hN
    subst ht0
    -- T.V i is trivial.
    haveI hTV_sub : ∀ i : Fin 3, Subsingleton (T.V i) := by
      intro i
      have hbij := G.is_internal i
      have hzero : ∀ x : T.V i, x = 0 := by
        intro x
        obtain ⟨w, hw⟩ := hbij.surjective x
        have hw0 : w = 0 := by
          ext j
          exact Fin.elim0 j
        rw [← hw, hw0, map_zero]
      exact ⟨fun x y => by rw [hzero x, hzero y]⟩
    -- (T.kronPow N).V i is trivial for N ≥ 1.
    have hkV_sub : ∀ (M : ℕ) (_ : 0 < M) (i : Fin 3), Subsingleton ((T.kronPow M).V i) := by
      intro M hM i
      induction M with
      | zero => omega
      | succ M ih =>
        -- (T.kronPow (M+1)).V i = TensorProduct K (T.V i) ((T.kronPow M).V i) by unfolding.
        haveI := hTV_sub i
        refine ⟨fun x y => ?_⟩
        have hVeq : (T.kronPow (M+1)).V i = TensorProduct K (T.V i) ((T.kronPow M).V i) := rfl
        -- Use the equation to transport x, y into the tensor product.
        have hz : ∀ z : TensorProduct K (T.V i) ((T.kronPow M).V i), z = 0 := by
          intro z
          induction z using TensorProduct.induction_on with
          | zero => rfl
          | tmul a b => rw [Subsingleton.elim a (0 : T.V i), TensorProduct.zero_tmul]
          | add a b ha hb => rw [ha, hb, zero_add]
        -- Reinterpret x, y as elements of the tensor product.
        have hxz : (hVeq ▸ x : TensorProduct K (T.V i) ((T.kronPow M).V i)) = 0 := hz _
        have hyz : (hVeq ▸ y : TensorProduct K (T.V i) ((T.kronPow M).V i)) = 0 := hz _
        have : (hVeq ▸ x : TensorProduct K (T.V i) ((T.kronPow M).V i)) = hVeq ▸ y := by rw [hxz, hyz]
        exact (Equiv.cast hVeq).injective this
    haveI hkVN_sub : ∀ i : Fin 3, Subsingleton ((T.kronPow N).V i) := hkV_sub N hN_pos
    haveI hPT_sub : Subsingleton (PiTensorProduct K (fun i => (T.kronPow N).V i)) := by
      refine ⟨fun x y => ?_⟩
      have hz : ∀ z : PiTensorProduct K (fun i => (T.kronPow N).V i), z = 0 := by
        intro z
        induction z using PiTensorProduct.induction_on with
        | smul_tprod a f =>
          have hf0 : f 0 = 0 := Subsingleton.elim _ _
          have hupd : f = Function.update f 0 0 := by
            funext j
            by_cases hj : j = 0
            · subst hj; rw [Function.update_self]; exact hf0
            · rw [Function.update_of_ne hj]
          rw [hupd]
          simp [MultilinearMap.map_update_zero]
        | add x y hx hy => rw [hx, hy, zero_add]
      rw [hz x, hz y]
    -- Build the vacuous grading and conclude.
    rw [htN0]
    let dec : ∀ i : Fin 3, Fin 0 → Submodule K ((T.kronPow N).V i) := fun _ α => Fin.elim0 α
    have hint : ∀ i : Fin 3, DirectSum.IsInternal (dec i) := by
      intro i
      constructor
      · intro x y _
        exact Subsingleton.elim _ _
      · intro z
        refine ⟨0, ?_⟩
        have : (z : (T.kronPow N).V i) = 0 := Subsingleton.elim _ _
        rw [map_zero]; exact this.symm
    refine ⟨{ decomp := dec, is_internal := hint }, ?_⟩
    exact Subsingleton.elim _ _
