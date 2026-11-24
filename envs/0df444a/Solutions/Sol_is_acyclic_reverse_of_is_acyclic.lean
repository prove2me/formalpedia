-- Prove2me | solution 1 for is_acyclic_reverse_of_is_acyclic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:50:24.582577+00:00
-- url     : https://prove2.me/submissions/f353bbf4-d507-40d5-820f-bf574d87aa40

module
public import Definitions.Def_ChipFiringWithLean_Config
public import Mathlib.Data.DFinsupp.Multiset
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty



set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution (G : CFGraph) (O : CFOrientation G)
    (h_acyclic : is_acyclic G O) :
  is_acyclic G (O.reverse G) := by
  intro p
  let q : DirectedPath O := {
    vertices := p.vertices.reverse,
    non_empty := by
      rw [List.length_reverse]
      exact p.non_empty,
    valid_edges := by
      have p_valid := p.valid_edges
      have hyp := List.isChain_reverse.mpr p_valid
      -- hyp : List.IsChain (flip (directed_edge G (CFOrientation.reverse G O))) p.vertices
      -- Need to show: List.IsChain (directed_edge G (CFOrientation.reverse G O)) p.vertices.reverse
      -- Since isChain_reverse gives us the flipped relation, we need to show
      -- flip (directed_edge G (CFOrientation.reverse G O)) = directed_edge G O
      convert hyp using 2
      ext a
      simp only [directed_edge, CFOrientation.reverse, Multiset.mem_map, Prod.exists,
          Prod.swap_prod_mk, Prod.mk.injEq, ↓existsAndEq, true_and, exists_eq_right]
  }
  have h_non_repeating_q : non_repeating q := h_acyclic q
  exact List.nodup_reverse.mp h_non_repeating_q
