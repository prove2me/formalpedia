-- Prove2me | solution 1 for infinite_ramsey_triples
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:43:47.523527+00:00
-- url     : https://prove2.me/submissions/9d849138-e29f-48e6-86d9-0d189c031934

module
public import Mathlib.Data.Finset.Card
public import Definitions.Def_LeanPool_NashWilliams_Data_Fintype_Pigeonhole
public import Definitions.Def_LeanPool_NashWilliams_Data_Nat_Nth
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Ramsey_Infinite
public import Theorems.Thm_infinite_ramsey_seq

set_option autoImplicit true
@[expose] public section
public section
open Set
noncomputable section
variable {κ : Type*}
theorem _root_.solution {κ : Type*} [Finite κ]
    (c : ∀ (m n l : ℕ), (m < n ∧ n < l) → κ) :
    ∃ (e : ℕ → ℕ), ∃ (he : StrictMono e), ∃ k : κ,
      ∀ h i j : ℕ, (hs : h < i ∧ i < j) →
        c (e h) (e i) (e j) ⟨he hs.1, he hs.2⟩ = k := by
  classical
  set d : κ := c 0 1 2 ⟨Nat.zero_lt_one, Nat.one_lt_two⟩ with hd
  set C : Finset ℕ → κ := fun t =>
    if h : t.Nonempty then
      if h2 : (t.erase (t.min' h)).Nonempty then
        if hh : t.min' h < (t.erase (t.min' h)).min' h2 ∧
                (t.erase (t.min' h)).min' h2 < t.max' h then
          c (t.min' h) ((t.erase (t.min' h)).min' h2) (t.max' h) hh
        else d
      else d
    else d with hC
  obtain ⟨e, he, k, hk⟩ := infinite_ramsey_seq 3 C
  refine ⟨e, he, k, fun p q r hpqr => ?_⟩
  obtain ⟨hpq, hqr⟩ := hpqr
  have hlt1 : e p < e q := he hpq
  have hlt2 : e q < e r := he hqr
  have hlt0 : e p < e r := lt_trans hlt1 hlt2
  set t : Finset ℕ := {e p, e q, e r} with ht
  have hmem_iff : ∀ y ∈ t, y = e p ∨ y = e q ∨ y = e r := by
    intro y hy; rw [ht] at hy
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hy
  have hep : e p ∈ t := by rw [ht]; exact Finset.mem_insert_self _ _
  have heq : e q ∈ t := by rw [ht]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have her : e r ∈ t := by
    rw [ht]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have htne : t.Nonempty := ⟨e p, hep⟩
  have hpq_ne : e p ≠ e q := ne_of_lt hlt1
  have hpr_ne : e p ≠ e r := ne_of_lt hlt0
  have hqr_ne : e q ≠ e r := ne_of_lt hlt2
  have htcard : t.card = 3 := by
    rw [ht, Finset.card_insert_of_notMem (by simp [hpq_ne, hpr_ne]),
        Finset.card_insert_of_notMem (by simp [hqr_ne]), Finset.card_singleton]
  have htsub : ↑t ⊆ Set.range e := by
    rw [ht]; intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [⟨p, rfl⟩, ⟨q, rfl⟩, ⟨r, rfl⟩]
  have hmin : t.min' htne = e p := by
    apply le_antisymm (Finset.min'_le _ _ hep)
    apply Finset.le_min'
    intro y hy; rcases hmem_iff y hy with rfl | rfl | rfl
    exacts [le_refl _, le_of_lt hlt1, le_of_lt hlt0]
  have hmax : t.max' htne = e r := by
    apply le_antisymm _ (Finset.le_max' _ _ her)
    apply Finset.max'_le
    intro y hy; rcases hmem_iff y hy with rfl | rfl | rfl
    exacts [le_of_lt hlt0, le_of_lt hlt2, le_refl _]
  -- the middle element is the least element of `t` with the minimum removed
  have hqmem : e q ∈ t.erase (t.min' htne) := by
    rw [Finset.mem_erase, hmin]; exact ⟨Ne.symm hpq_ne, heq⟩
  have H2 : (t.erase (t.min' htne)).Nonempty := ⟨e q, hqmem⟩
  have hmid : (t.erase (t.min' htne)).min' H2 = e q := by
    apply le_antisymm (Finset.min'_le _ _ hqmem)
    apply Finset.le_min'
    intro y hy
    rw [Finset.mem_erase, hmin] at hy
    obtain ⟨hyne, hyt⟩ := hy
    rcases hmem_iff y hyt with rfl | rfl | rfl
    · exact absurd rfl hyne
    · exact le_refl _
    · exact le_of_lt hlt2
  -- the ordering condition holds; evaluate `C t`
  have Hcond : t.min' htne < (t.erase (t.min' htne)).min' H2 ∧
      (t.erase (t.min' htne)).min' H2 < t.max' htne := by
    refine ⟨?_, ?_⟩
    · rw [hmid, hmin]; exact hlt1
    · rw [hmid, hmax]; exact hlt2
  have key : ∀ (A B D : ℕ) (pf : A < B ∧ B < D), A = e p → B = e q → D = e r →
      c A B D pf = c (e p) (e q) (e r) ⟨hlt1, hlt2⟩ := by
    rintro A B D pf rfl rfl rfl; rfl
  have hCt : C t = c (e p) (e q) (e r) ⟨hlt1, hlt2⟩ := by
    have hval : C t =
        c (t.min' htne) ((t.erase (t.min' htne)).min' H2) (t.max' htne) Hcond := by
      simp only [hC]
      rw [dif_pos htne, dif_pos H2, dif_pos Hcond]
    rw [hval]
    exact key _ _ _ Hcond hmin hmid hmax
  have hkt : C t = k := hk t htsub htcard
  rw [hCt] at hkt
  exact hkt
