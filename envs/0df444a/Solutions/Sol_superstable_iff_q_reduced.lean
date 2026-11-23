-- Prove2me | solution 1 for superstable_iff_q_reduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:45:34.527807+00:00
-- url     : https://prove2.me/submissions/bc63c861-cae5-4ad8-9114-993c6550ff53

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Config
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
public import Theorems.Thm_q_reduced_exists_lt_outdeg
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty



set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution (G : CFGraph) (q : G.V) (d : ℤ) (c : Config G q) :
  superstable G q c ↔ q_reduced G q (toDiv d c) := by
  dsimp only [superstable, ne_eq]
  constructor
  -- Forward direction
  intro h_superstable
  constructor
  -- Show c is nonnegative away from v
  intro v hv_ne_q
  dsimp only [toDiv, Pi.add_apply, Pi.smul_apply, Int.zsmul_eq_mul]
  simp only [ne_eq, hv_ne_q, not_false_eq_true, one_chip_apply_other', mul_zero, add_zero,
      ge_iff_le]
  exact c.non_negative v
  -- Show there is no nonempty legal set avoiding q
  intro S hq hS_nonempty hlegal
  have hS_subset : S ⊆ Vtilde q := by
    intro v hv_in_S
    simp only [Vtilde, Finset.mem_filter, mem_univ, true_and]
    exact fun hvq => hq (hvq ▸ hv_in_S)
  obtain ⟨v, hv_in_S, hv_outdeg⟩ := h_superstable S hS_subset hS_nonempty
  have h_v_ne_q : v ≠ q := by
    exact fun hvq => hq (hvq ▸ hv_in_S)
  have hge := hlegal v hv_in_S
  rw [eval_toDiv_ne_q d c h_v_ne_q] at hge
  omega
  -- Reverse direction
  intro h_q_reduced S hS_subset hS_nonempty
  have hq : q ∉ S := by
    intro hq_in_S
    have := hS_subset hq_in_S
    simp only [Vtilde, Finset.mem_filter, mem_univ, ne_eq, not_true_eq_false,
      and_false] at this
  obtain ⟨v, hv_in_S, hv_outdeg⟩ :=
    h_q_reduced.exists_lt_outdeg hq hS_nonempty
  use v
  refine ⟨hv_in_S, ?_⟩
  have h_v_neq_q : v ≠ q := fun hvq => hq (hvq ▸ hv_in_S)
  rw [eval_toDiv_ne_q d c h_v_neq_q] at hv_outdeg
  exact hv_outdeg
