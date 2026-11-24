-- Prove2me | solution 1 for superstable_of_divisor_negative_k
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:53:09.615801+00:00
-- url     : https://prove2.me/submissions/c9da94fb-4a87-4e57-b677-407c7fd4adbc

module
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Definitions.Def_ChipFiringWithLean_Rank
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
public import Theorems.Thm_config_eff
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
public import Theorems.Thm_winnable_equiv_winnable
public import Theorems.Thm_winnable_of_effective
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty



set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution (G : CFGraph) (q : G.V) (D : CFDiv G) :
  ¬(winnable G D) →
  ∀ (c : Config G q) (k : ℤ),
    linear_equiv G D (c.chips + k • (one_chip q)) →
    superstable G q c →
    k < 0 := by
  intro h_not_winnable c k h_equiv h_super
  contrapose! h_not_winnable with k_nonneg
  let D' := c.chips + k • (one_chip q)
  have D'_eff : effective D' := by
    rw [show D' = toDiv (config_degree c + k) c by
      dsimp only [D']
      rw [toDiv_config_degree_add]]
    exact (config_eff (config_degree c + k) c).2 (by linarith)
  have h_winnable_D' : winnable G D' := winnable_of_effective G D' D'_eff
  exact winnable_equiv_winnable G D' D h_winnable_D' h_equiv.symm
