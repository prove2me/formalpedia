-- Prove2me | solution 1 for mme_tau_enum_card_eq_multinomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-06-05T03:33:51.113507+00:00
-- url     : https://prove2.me/submissions/feabf3d1-fa29-431a-882e-78ad06afa83e

import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Fintype.Pi
import Definitions.Def_mme_empirical_dist

open BigOperators


/-! # `Sol_mme_tau_enum_card_eq_multinomial` — multinomial counting of τ-strings.

Sorry-free closure of the leaf
`Theorems.Thm_mme_tau_enum_card_eq_multinomial`. -/

open BigOperators Finset

universe u

namespace MMETauEnum

/-- Reconstruct `τ : Fin N → α` from a chosen subset `T` (positions
mapped to `a`) and a function `τ' : Fin n → α` on the complement
(interpreted via the order embedding `Tᶜ.orderEmbOfFin`). -/
noncomputable def reconstructTau {α : Type u} [DecidableEq α] {N n : ℕ}
    (T : Finset (Fin N)) (hT : Tᶜ.card = n)
    (a : α) (τ' : Fin n → α) : Fin N → α := fun k =>
  if hkT : k ∈ T then a
  else τ' ((Tᶜ.orderIsoOfFin hT).symm ⟨k, Finset.mem_compl.mpr hkT⟩)

/-- The restriction of `τ` to the complement of `T`, re-indexed as a
function on `Fin n` via the order embedding. -/
noncomputable def restrictTau {α : Type u} {N n : ℕ}
    (T : Finset (Fin N)) (hT : Tᶜ.card = n)
    (τ : Fin N → α) : Fin n → α :=
  fun i => τ (Tᶜ.orderEmbOfFin hT i)

lemma restrictTau_apply {α : Type u} {N n : ℕ}
    (T : Finset (Fin N)) (hT : Tᶜ.card = n) (τ : Fin N → α) (i : Fin n) :
    restrictTau T hT τ i = τ (Tᶜ.orderEmbOfFin hT i) := rfl

lemma reconstructTau_of_mem {α : Type u} [DecidableEq α] {N n : ℕ}
    (T : Finset (Fin N)) (hT : Tᶜ.card = n) (a : α) (τ' : Fin n → α)
    {k : Fin N} (hk : k ∈ T) :
    reconstructTau T hT a τ' k = a := by
  unfold reconstructTau; rw [dif_pos hk]

lemma reconstructTau_of_notMem {α : Type u} [DecidableEq α] {N n : ℕ}
    (T : Finset (Fin N)) (hT : Tᶜ.card = n) (a : α) (τ' : Fin n → α)
    {k : Fin N} (hk : k ∉ T) :
    reconstructTau T hT a τ' k =
      τ' ((Tᶜ.orderIsoOfFin hT).symm ⟨k, Finset.mem_compl.mpr hk⟩) := by
  unfold reconstructTau; rw [dif_neg hk]

lemma orderEmbOfFin_compl_notMem {N n : ℕ} (T : Finset (Fin N))
    (hT : Tᶜ.card = n) (i : Fin n) : (Tᶜ.orderEmbOfFin hT i) ∉ T := by
  have hMem : Tᶜ.orderEmbOfFin hT i ∈ Tᶜ :=
    Finset.orderEmbOfFin_mem Tᶜ hT i
  rwa [Finset.mem_compl] at hMem

/-- Key identity: `Tᶜ.orderEmbOfFin hT i = ↑(Tᶜ.orderIsoOfFin hT i)`. -/
lemma orderEmb_eq_orderIso_coe {N n : ℕ} (T : Finset (Fin N))
    (hT : Tᶜ.card = n) (i : Fin n) :
    Tᶜ.orderEmbOfFin hT i = (Tᶜ.orderIsoOfFin hT i : Fin N) := rfl

/-- The order embedding composed with the inverse iso recovers the
underlying element. -/
lemma orderEmb_symm_of_compl {N n : ℕ} (T : Finset (Fin N)) (hT : Tᶜ.card = n)
    (k : Fin N) (hkc : k ∈ Tᶜ) :
    Tᶜ.orderEmbOfFin hT ((Tᶜ.orderIsoOfFin hT).symm ⟨k, hkc⟩) = k := by
  show ((Tᶜ.orderIsoOfFin hT ((Tᶜ.orderIsoOfFin hT).symm ⟨k, hkc⟩)) : Fin N) = k
  rw [OrderIso.apply_symm_apply]

/-- The inverse iso applied to an orderEmb output recovers the index. -/
lemma orderIso_symm_orderEmb {N n : ℕ} (T : Finset (Fin N)) (hT : Tᶜ.card = n)
    (i : Fin n) (h : Tᶜ.orderEmbOfFin hT i ∈ Tᶜ) :
    (Tᶜ.orderIsoOfFin hT).symm ⟨Tᶜ.orderEmbOfFin hT i, h⟩ = i := by
  have : Tᶜ.orderEmbOfFin hT i = ((Tᶜ.orderIsoOfFin hT i) : Fin N) := rfl
  -- Use Subtype.ext: ⟨Tᶜ.orderEmbOfFin hT i, h⟩ = Tᶜ.orderIsoOfFin hT i
  have hsubeq : (⟨Tᶜ.orderEmbOfFin hT i, h⟩ : {x // x ∈ Tᶜ}) =
      Tᶜ.orderIsoOfFin hT i := by
    apply Subtype.ext; rfl
  rw [hsubeq, OrderIso.symm_apply_apply]

@[simp] lemma reconstructTau_orderEmb {α : Type u} [DecidableEq α] {N n : ℕ}
    (T : Finset (Fin N)) (hT : Tᶜ.card = n) (a : α) (τ' : Fin n → α) (i : Fin n) :
    reconstructTau T hT a τ' (Tᶜ.orderEmbOfFin hT i) = τ' i := by
  have hk := orderEmbOfFin_compl_notMem T hT i
  rw [reconstructTau_of_notMem _ _ _ _ hk]
  have hMem : Tᶜ.orderEmbOfFin hT i ∈ Tᶜ := Finset.mem_compl.mpr hk
  rw [orderIso_symm_orderEmb T hT i hMem]

end MMETauEnum

open MMETauEnum

/-- Sub-lemma: empirical distribution of `restrictTau` matches that of `τ`
on elements `σ ≠ a` when `τ`'s preimage of `a` is exactly `T`. -/
private lemma empirical_restrict_eq {α : Type u} [Fintype α] [DecidableEq α]
    {N n : ℕ} (T : Finset (Fin N)) (hTcompl : Tᶜ.card = n) (a : α)
    (τ : Fin N → α) (hτT : Finset.univ.filter (fun k : Fin N => τ k = a) = T)
    (σ : α) (hσne : σ ≠ a) :
    empiricalDist (restrictTau T hTcompl τ) σ = empiricalDist τ σ := by
  classical
  unfold empiricalDist
  refine Finset.card_bij'
    (fun i _ => Tᶜ.orderEmbOfFin hTcompl i)
    (fun j hj => by
      classical
      refine (Tᶜ.orderIsoOfFin hTcompl).symm ⟨j, ?_⟩
      rw [Finset.mem_compl]
      intro hjT
      rw [Finset.mem_filter] at hj
      have hjmem : j ∈ Finset.univ.filter (fun k : Fin N => τ k = a) := by
        rw [hτT]; exact hjT
      rw [Finset.mem_filter] at hjmem
      -- hj.2 : τ j = σ, hjmem.2 : τ j = a, σ ≠ a contradiction
      exact hσne (hj.2.symm.trans hjmem.2))
    ?fst ?snd ?li ?ri
  · intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have : restrictTau T hTcompl τ i = τ (Tᶜ.orderEmbOfFin hTcompl i) := rfl
    rw [← this]; exact hi.2
  · intro j hj
    rw [Finset.mem_filter] at hj ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have hjc : j ∈ Tᶜ := by
      rw [Finset.mem_compl]
      intro hjT
      have hjmem : j ∈ Finset.univ.filter (fun k : Fin N => τ k = a) := by
        rw [hτT]; exact hjT
      rw [Finset.mem_filter] at hjmem
      exact hσne (hj.2.symm.trans hjmem.2)
    show restrictTau T hTcompl τ
      ((Tᶜ.orderIsoOfFin hTcompl).symm ⟨j, hjc⟩) = σ
    rw [restrictTau_apply, orderEmb_symm_of_compl]
    exact hj.2
  · intro i _
    have hMem : Tᶜ.orderEmbOfFin hTcompl i ∈ Tᶜ :=
      Finset.mem_compl.mpr (orderEmbOfFin_compl_notMem T hTcompl i)
    exact orderIso_symm_orderEmb T hTcompl i hMem
  · intro j hj
    rw [Finset.mem_filter] at hj
    have hjc : j ∈ Tᶜ := by
      rw [Finset.mem_compl]
      intro hjT
      have hjmem : j ∈ Finset.univ.filter (fun k : Fin N => τ k = a) := by
        rw [hτT]; exact hjT
      rw [Finset.mem_filter] at hjmem
      exact hσne (hj.2.symm.trans hjmem.2)
    exact orderEmb_symm_of_compl T hTcompl j hjc

/-- Sub-lemma: empirical distribution of `reconstructTau` at a non-`a`
symbol equals that of the underlying `τ'`. -/
private lemma empirical_reconstruct_ne {α : Type u} [Fintype α] [DecidableEq α]
    {N n : ℕ} (T : Finset (Fin N)) (hTcompl : Tᶜ.card = n) (a : α)
    (τ' : Fin n → α) (σ : α) (hσne : σ ≠ a) :
    empiricalDist (reconstructTau T hTcompl a τ') σ = empiricalDist τ' σ := by
  classical
  unfold empiricalDist
  refine Finset.card_bij'
    (fun k hk => by
      classical
      refine (Tᶜ.orderIsoOfFin hTcompl).symm ⟨k, ?_⟩
      rw [Finset.mem_compl]
      intro hkT
      rw [Finset.mem_filter] at hk
      have := reconstructTau_of_mem T hTcompl a τ' hkT
      exact hσne (hk.2.symm.trans this))
    (fun i _ => Tᶜ.orderEmbOfFin hTcompl i)
    ?fst ?snd ?li ?ri
  · intro k hk
    rw [Finset.mem_filter] at hk ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have hkT : k ∉ T := by
      intro hkT
      have := reconstructTau_of_mem T hTcompl a τ' hkT
      exact hσne (hk.2.symm.trans this)
    rw [reconstructTau_of_notMem _ _ _ _ hkT] at hk
    exact hk.2
  · intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [reconstructTau_orderEmb]
    exact hi.2
  · intro k hk
    rw [Finset.mem_filter] at hk
    have hkT : k ∉ T := by
      intro hkT
      have := reconstructTau_of_mem T hTcompl a τ' hkT
      exact hσne (hk.2.symm.trans this)
    exact orderEmb_symm_of_compl T hTcompl k (Finset.mem_compl.mpr hkT)
  · intro i _
    have hMem : Tᶜ.orderEmbOfFin hTcompl i ∈ Tᶜ :=
      Finset.mem_compl.mpr (orderEmbOfFin_compl_notMem T hTcompl i)
    exact orderIso_symm_orderEmb T hTcompl i hMem

/-- Sub-lemma: empirical distribution of `reconstructTau` at `a` equals `T.card`. -/
private lemma empirical_reconstruct_at {α : Type u} [Fintype α] [DecidableEq α]
    {N n : ℕ} (T : Finset (Fin N)) (hTcompl : Tᶜ.card = n) (a : α)
    (τ' : Fin n → α) (hτ'_in_s : ∀ i, τ' i ∈ (Finset.univ : Finset α) \ {a}) :
    empiricalDist (reconstructTau T hTcompl a τ') a = T.card := by
  classical
  unfold empiricalDist
  have : (Finset.univ.filter
      (fun k : Fin N => reconstructTau T hTcompl a τ' k = a)) = T := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hk : k ∈ T
    · refine ⟨fun _ => hk, fun _ => ?_⟩
      exact reconstructTau_of_mem T hTcompl a τ' hk
    · refine ⟨fun habs => ?_, fun h => (hk h).elim⟩
      rw [reconstructTau_of_notMem _ _ _ _ hk] at habs
      exfalso
      have hmem := hτ'_in_s ((Tᶜ.orderIsoOfFin hTcompl).symm
        ⟨k, Finset.mem_compl.mpr hk⟩)
      rw [Finset.mem_sdiff] at hmem
      exact hmem.2 (by simp [habs])
  rw [this]

/-- Auxiliary: the cardinality of a single fiber (functions with fixed
preimage of `a`) equals the smaller multinomial. -/
private lemma fiber_card_eq {α : Type u} [Fintype α] [DecidableEq α]
    {N : ℕ} (a : α) (s : Finset α) (ha : a ∉ s) (μ : α → ℕ)
    (n : ℕ) (T : Finset (Fin N)) (hTk : T.card = μ a) (hNk : N = μ a + n)
    (IH_count :
      (Finset.univ.filter
          (fun τ' : Fin n → α => (∀ k, τ' k ∈ s) ∧
            (∀ σ ∈ s, empiricalDist τ' σ = μ σ))).card =
        Nat.multinomial s μ) :
    (Finset.univ.filter (fun τ : Fin N → α =>
        (∀ k, τ k ∈ insert a s) ∧
        (∀ σ ∈ insert a s, empiricalDist τ σ = μ σ) ∧
        Finset.univ.filter (fun k : Fin N => τ k = a) = T)).card =
      Nat.multinomial s μ := by
  classical
  have hNc : (Finset.univ : Finset (Fin N)).card = N := by simp
  have hTcompl : Tᶜ.card = n := by
    have hcompl : Tᶜ.card = (Finset.univ : Finset (Fin N)).card - T.card :=
      Finset.card_compl T
    rw [hcompl, hTk, hNc, hNk]; omega
  rw [← IH_count]
  refine Finset.card_bij'
    (fun τ _ => restrictTau T hTcompl τ)
    (fun τ' _ => reconstructTau T hTcompl a τ')
    ?fwd ?bwd ?linv ?rinv
  ----------------------------------------------------------------
  -- forward maps to s-fiber
  ----------------------------------------------------------------
  · rintro τ hτ
    rw [Finset.mem_filter] at hτ
    obtain ⟨_, hτimg, hτemp, hτT⟩ := hτ
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · -- image in s
      intro i
      have hNotInT : Tᶜ.orderEmbOfFin hTcompl i ∉ T :=
        orderEmbOfFin_compl_notMem T hTcompl i
      have himg := hτimg (Tᶜ.orderEmbOfFin hTcompl i)
      rcases Finset.mem_insert.mp himg with heq | hin
      · exfalso
        apply hNotInT
        have hmem : Tᶜ.orderEmbOfFin hTcompl i ∈
            Finset.univ.filter (fun j : Fin N => τ j = a) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩
        rw [hτT] at hmem; exact hmem
      · -- restrictTau τ i = τ (orderEmb i) ∈ s
        change τ (Tᶜ.orderEmbOfFin hTcompl i) ∈ s
        exact hin
    · intro σ hσ
      have hσne : σ ≠ a := fun h => ha (h ▸ hσ)
      rw [empirical_restrict_eq T hTcompl a τ hτT σ hσne]
      exact hτemp σ (Finset.mem_insert_of_mem hσ)
  ----------------------------------------------------------------
  -- backward maps to full fiber
  ----------------------------------------------------------------
  · rintro τ' hτ'
    rw [Finset.mem_filter] at hτ'
    obtain ⟨_, hτ'img, hτ'emp⟩ := hτ'
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
    · -- image in insert a s
      intro k
      show reconstructTau T hTcompl a τ' k ∈ insert a s
      by_cases hk : k ∈ T
      · rw [reconstructTau_of_mem _ _ _ _ hk]
        exact Finset.mem_insert_self a s
      · rw [reconstructTau_of_notMem _ _ _ _ hk]
        exact Finset.mem_insert_of_mem (hτ'img _)
    · -- empirical = μ
      intro σ hσ
      show empiricalDist (reconstructTau T hTcompl a τ') σ = μ σ
      rcases Finset.mem_insert.mp hσ with heq | hin
      · subst heq
        have hτ'_sdiff : ∀ i, τ' i ∈ (Finset.univ : Finset α) \ {σ} := by
          intro i
          rw [Finset.mem_sdiff]
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [Finset.mem_singleton]
          intro h
          exact ha (h ▸ hτ'img i)
        rw [empirical_reconstruct_at T hTcompl σ τ' hτ'_sdiff, hTk]
      · have hσne : σ ≠ a := fun h => ha (h ▸ hin)
        rw [empirical_reconstruct_ne T hTcompl a τ' σ hσne]
        exact hτ'emp σ hin
    · -- filter (τ · = a) = T
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hk : k ∈ T
      · refine ⟨fun _ => hk, fun _ => ?_⟩
        show reconstructTau T hTcompl a τ' k = a
        exact reconstructTau_of_mem _ _ _ _ hk
      · refine ⟨fun habs => ?_, fun h => (hk h).elim⟩
        change reconstructTau T hTcompl a τ' k = a at habs
        rw [reconstructTau_of_notMem _ _ _ _ hk] at habs
        exfalso
        exact ha (habs ▸ hτ'img _)
  ----------------------------------------------------------------
  -- left inverse: reconstruct ∘ restrict = id
  ----------------------------------------------------------------
  · intro τ hτ
    rw [Finset.mem_filter] at hτ
    obtain ⟨_, _, _, hτT⟩ := hτ
    funext k
    show reconstructTau T hTcompl a (restrictTau T hTcompl τ) k = τ k
    by_cases hk : k ∈ T
    · rw [reconstructTau_of_mem _ _ _ _ hk]
      have : k ∈ Finset.univ.filter (fun j : Fin N => τ j = a) := by
        rw [hτT]; exact hk
      rw [Finset.mem_filter] at this
      exact this.2.symm
    · rw [reconstructTau_of_notMem _ _ _ _ hk]
      show restrictTau T hTcompl τ
        ((Tᶜ.orderIsoOfFin hTcompl).symm ⟨k, Finset.mem_compl.mpr hk⟩) = τ k
      rw [restrictTau_apply, orderEmb_symm_of_compl]
  ----------------------------------------------------------------
  -- right inverse: restrict ∘ reconstruct = id
  ----------------------------------------------------------------
  · intro τ' _
    funext i
    show restrictTau T hTcompl (reconstructTau T hTcompl a τ') i = τ' i
    rw [restrictTau_apply, reconstructTau_orderEmb]

/-- Generalized version: works for any μ supported on S and any N matching its sum. -/
private theorem solution_aux {α : Type u} [Fintype α] [DecidableEq α]
    (S : Finset α) :
    ∀ (μ : α → ℕ) (_hsupp : ∀ σ : α, μ σ ≠ 0 → σ ∈ S)
      (N : ℕ) (_hsum : ∑ σ ∈ S, μ σ = N),
    (Finset.univ.filter
        (fun τ : Fin N → α => (∀ k, τ k ∈ S) ∧
          (∀ σ ∈ S, empiricalDist τ σ = μ σ))).card =
      Nat.multinomial S μ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro μ _hsupp N hsum
    simp at hsum
    subst hsum
    rw [Nat.multinomial_empty]
    have hfilter_eq : (Finset.univ.filter
        (fun τ : Fin 0 → α => (∀ k, τ k ∈ (∅ : Finset α)) ∧
          (∀ σ ∈ (∅ : Finset α), empiricalDist τ σ = μ σ))) =
        (Finset.univ : Finset (Fin 0 → α)) := by
      apply Finset.filter_true_of_mem
      intro τ _
      refine ⟨?_, ?_⟩
      · intro k; exact k.elim0
      · intro σ hσ; exact (Finset.notMem_empty _ hσ).elim
    rw [hfilter_eq, Finset.card_univ]
    rw [Fintype.card_fun, Fintype.card_fin]
    simp
  | insert a s ha IH =>
    intro μ hsupp N hsum
    set k := μ a with hk_def
    set n := ∑ σ ∈ s, μ σ with hn_def
    have hNk : N = k + n := by
      rw [← hsum, Finset.sum_insert ha]
    let μ' : α → ℕ := fun σ => if σ = a then 0 else μ σ
    have hsum_s' : ∑ σ ∈ s, μ' σ = n := by
      apply Finset.sum_congr rfl
      intro σ hσ
      have : σ ≠ a := fun h => ha (h ▸ hσ)
      simp [μ', this]
    have hsupp' : ∀ σ : α, μ' σ ≠ 0 → σ ∈ s := by
      intro σ hσ
      by_cases hsa : σ = a
      · simp [μ', hsa] at hσ
      · simp [μ', hsa] at hσ
        rcases Finset.mem_insert.mp (hsupp σ hσ) with h | h
        · exact (hsa h).elim
        · exact h
    have IH_n := IH μ' hsupp' n hsum_s'
    have hmulti_eq : Nat.multinomial s μ = Nat.multinomial s μ' := by
      apply Nat.multinomial_congr
      intro σ hσ
      have : σ ≠ a := fun h => ha (h ▸ hσ)
      simp [μ', this]
    have IH_count : (Finset.univ.filter
        (fun τ : Fin n → α => (∀ kk, τ kk ∈ s) ∧
          (∀ σ ∈ s, empiricalDist τ σ = μ σ))).card =
        Nat.multinomial s μ := by
      rw [hmulti_eq, ← IH_n]
      congr 1
      ext τ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        intro σ hσ
        have hne : σ ≠ a := fun h => ha (h ▸ hσ)
        rw [h2 σ hσ]; simp [μ', hne]
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        intro σ hσ
        have hne : σ ≠ a := fun h => ha (h ▸ hσ)
        have := h2 σ hσ
        simp [μ', hne] at this
        exact this
    have hLHS : (Finset.univ.filter
        (fun τ : Fin N → α => (∀ kk, τ kk ∈ insert a s) ∧
          (∀ σ ∈ insert a s, empiricalDist τ σ = μ σ))).card =
        ∑ T ∈ Finset.powersetCard k (Finset.univ : Finset (Fin N)),
          (Finset.univ.filter (fun τ : Fin N → α =>
            (∀ kk, τ kk ∈ insert a s) ∧
            (∀ σ ∈ insert a s, empiricalDist τ σ = μ σ) ∧
            Finset.univ.filter (fun kk : Fin N => τ kk = a) = T)).card := by
      have hmaps : Set.MapsTo
          (fun τ : Fin N → α => Finset.univ.filter (fun kk : Fin N => τ kk = a))
          ((Finset.univ.filter
              (fun τ : Fin N → α => (∀ kk, τ kk ∈ insert a s) ∧
                (∀ σ ∈ insert a s, empiricalDist τ σ = μ σ))) : Set (Fin N → α))
          ((Finset.powersetCard k (Finset.univ : Finset (Fin N))) :
            Set (Finset (Fin N))) := by
        intro τ hτ
        rw [Finset.mem_coe, Finset.mem_filter] at hτ
        rw [Finset.mem_coe, Finset.mem_powersetCard]
        obtain ⟨_, _, hemp⟩ := hτ
        refine ⟨Finset.subset_univ _, ?_⟩
        have := hemp a (Finset.mem_insert_self a s)
        unfold empiricalDist at this
        exact this
      rw [Finset.card_eq_sum_card_fiberwise hmaps]
      apply Finset.sum_congr rfl
      intro T _
      congr 1
      ext τ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_assoc]
    rw [hLHS]
    have hfiber : ∀ T ∈ Finset.powersetCard k (Finset.univ : Finset (Fin N)),
        (Finset.univ.filter (fun τ : Fin N → α =>
          (∀ kk, τ kk ∈ insert a s) ∧
          (∀ σ ∈ insert a s, empiricalDist τ σ = μ σ) ∧
          Finset.univ.filter (fun kk : Fin N => τ kk = a) = T)).card =
            Nat.multinomial s μ := by
      intro T hT
      rw [Finset.mem_powersetCard] at hT
      obtain ⟨_, hTk⟩ := hT
      exact fiber_card_eq a s ha μ n T hTk hNk IH_count
    rw [Finset.sum_congr rfl hfiber]
    rw [Finset.sum_const, Finset.card_powersetCard]
    rw [Finset.card_univ, Fintype.card_fin]
    rw [Nat.multinomial_insert ha]
    rw [hNk, smul_eq_mul]

/-- The τ-enumeration cardinality formula. -/
theorem solution {α : Type u} [Fintype α] [DecidableEq α]
    (S : Finset α) (μ : α → ℕ)
    (_hsupp : ∀ σ : α, μ σ ≠ 0 → σ ∈ S)
    (N : ℕ) (_hsum : ∑ σ ∈ S, μ σ = N) :
    (Finset.univ.filter
        (fun τ : Fin N → α => (∀ k, τ k ∈ S) ∧
          (∀ σ ∈ S, empiricalDist τ σ = μ σ))).card =
      Nat.multinomial S μ :=
  solution_aux S μ _hsupp N _hsum
