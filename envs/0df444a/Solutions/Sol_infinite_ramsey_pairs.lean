-- Prove2me | solution 1 for infinite_ramsey_pairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:43:43.48353+00:00
-- url     : https://prove2.me/submissions/fe374d3c-465b-4645-8256-f8463eef5215

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
theorem _root_.solution {κ : Type*} [Finite κ] (c : ∀ (m n : ℕ), m < n → κ) :
    ∃ (e : ℕ → ℕ), ∃ (he : StrictMono e), ∃ k : κ,
      ∀ i j : ℕ, (h : i < j) → c (e i) (e j) (he h) = k := by
  classical
  -- Colour a finite set by `c` of its min and max (junk value elsewhere).
  set d : κ := c 0 1 Nat.zero_lt_one with hd
  set C : Finset ℕ → κ := fun t =>
    if h : t.Nonempty then
      if hlt : t.min' h < t.max' h then c (t.min' h) (t.max' h) hlt else d
    else d with hC
  obtain ⟨e, he, k, hk⟩ := infinite_ramsey_seq 2 C
  refine ⟨e, he, k, fun i j hij => ?_⟩
  have hlt : e i < e j := he hij
  set t : Finset ℕ := {e i, e j} with ht
  have hij_ne : e i ∉ ({e j} : Finset ℕ) := by simp [ne_of_lt hlt]
  have htcard : t.card = 2 := by
    rw [ht, Finset.card_insert_of_notMem hij_ne, Finset.card_singleton]
  have htne : t.Nonempty := ⟨e i, by rw [ht]; exact Finset.mem_insert_self _ _⟩
  have htsub : ↑t ⊆ Set.range e := by
    rw [ht]; intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    exacts [⟨i, rfl⟩, ⟨j, rfl⟩]
  have hei_mem : e i ∈ t := by rw [ht]; exact Finset.mem_insert_self _ _
  have hej_mem : e j ∈ t := by rw [ht]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hmem_iff : ∀ y ∈ t, y = e i ∨ y = e j := by
    intro y hy; rw [ht] at hy
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hy
  have hmin : t.min' htne = e i := by
    apply le_antisymm (Finset.min'_le _ _ hei_mem)
    apply Finset.le_min'
    intro y hy; rcases hmem_iff y hy with rfl | rfl
    exacts [le_refl _, le_of_lt hlt]
  have hmax : t.max' htne = e j := by
    apply le_antisymm _ (Finset.le_max' _ _ hej_mem)
    apply Finset.max'_le
    intro y hy; rcases hmem_iff y hy with rfl | rfl
    exacts [le_of_lt hlt, le_refl _]
  have hCt : C t = c (e i) (e j) hlt := by
    have h1 : C t = if hlt' : t.min' htne < t.max' htne
        then c (t.min' htne) (t.max' htne) hlt' else d := by
      rw [hC]; simp only [htne, dif_pos]
    rw [h1, hmin, hmax, dif_pos hlt]
  have hkt : C t = k := hk t htsub htcard
  rw [hCt] at hkt
  exact hkt
