-- Prove2me | solution 1 for inf_graph_ramsey
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:50:21.793828+00:00
-- url     : https://prove2.me/submissions/8539360c-da69-4283-a2f0-441b63a32556

import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic
import Definitions.Def_AutomataTheory_Mathlib_InfGraphRamsey
import Theorems.Thm_selection_seq_prop

set_option autoImplicit true
open Function Set
open Classical
variable {Color Vertex : Type*} [Finite Color]
variable (color : (e : Edge) → Color)
variable [Infinite Vertex]
theorem _root_.solution :
    ∃ c : Color, ∃ s : Set Vertex, s.Infinite ∧ ∀ e : Edge (Vertex := Vertex), e.card = 2 → (e : Set Vertex) ⊆ s → color e = c := by
  obtain ⟨vs, v, c, h_sel⟩ := selection_seq_prop color
  simp only [forall_and] at h_sel
  obtain ⟨h_vs, h_v, h_c⟩ := h_sel
  have h_lem1 : ∀ m n, m < n → v n ∈ vs m := by
    intro m n h_m_n
    suffices h1 : (⋂ m < n, vs m) ⊆ vs m by aesop
    exact biInter_subset_of_mem h_m_n
  obtain ⟨c', s', h_s'_inf, h_s'_col⟩ : ∃ c' : Color, ∃ s' : Set ℕ, s'.Infinite ∧ ∀ n ∈ s', c n = c' := by
    obtain ⟨c', s', h_s'_inf, _, h_s'col⟩ := AutomataTheory.Compatibility.pigeonhole_principle c infinite_univ
    use c', s'
  use c', (v '' s')
  have h_v_inj : Injective v := by
    intro m n h_v_eq
    by_contra h_contra
    wlog h : m < n generalizing m n with h'
    · exact h' h_v_eq.symm (by omega) (by omega)
    have := h_lem1 m n h
    have := h_v m
    aesop
  constructor
  · exact Infinite.image (injOn_of_injective h_v_inj (s := s')) h_s'_inf
  simp only [Finset.card_eq_two]
  rintro e ⟨v1, v2, h_ne, rfl⟩
  simp [pair_subset_iff]
  rintro m h_m rfl n h_n rfl
  have h_ne' : m ≠ n := by by_contra h_contra ; simp [h_contra] at h_ne
  wlog h : m < n generalizing m n with h'
  · rw [Finset.pair_comm]
    exact h' n h_n m h_m h_ne.symm h_ne'.symm (by omega)
  simp [h_c m (v n) (h_lem1 m n h), h_s'_col m h_m]
