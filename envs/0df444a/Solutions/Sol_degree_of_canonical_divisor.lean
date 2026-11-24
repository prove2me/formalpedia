-- Prove2me | solution 1 for degree_of_canonical_divisor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:50:12.25091+00:00
-- url     : https://prove2.me/submissions/a59ed3de-12f6-48f6-93a6-b4e9dbde765c

module
public import Definitions.Def_ChipFiringWithLean_Config
public import Mathlib.Data.DFinsupp.Multiset
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
public import Theorems.Thm_sum_vertex_degree_eq_twice_card_edges
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty



set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution (G : CFGraph) :
    deg (canonical_divisor G) = 2 * genus G - 2 := by
  -- Use sum_sub_distrib to split the sum
  have h1 : ∑ v, (canonical_divisor G v) =
            ∑ v, vertex_degree G v - 2 * Fintype.card G.V := by
    unfold canonical_divisor
    rw [sum_sub_distrib]
    simp only [sum_const, card_univ, Int.nsmul_eq_mul, sub_right_inj]
    ring
  dsimp only [deg, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [h1]

  -- Use the fact that sum of vertex degrees = 2|E|
  have h2 : ∑ v, vertex_degree G v = 2 * Multiset.card G.edges := by
    exact sum_vertex_degree_eq_twice_card_edges G
  rw [h2]

  -- Use genus definition: g = |E| - |G.V| + 1
  rw [genus]

  ring
