-- Prove2me | solution 1 for winnable_of_effective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:46:15.673802+00:00
-- url     : https://prove2.me/submissions/1df28c3d-48b7-4967-a1e1-9657d24e7fc6

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Rank

set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution (G : CFGraph) (D : CFDiv G) (h_eff : effective D) : winnable G D := by
  exact ⟨D, h_eff, by
    unfold linear_equiv
    rw [sub_self]
    exact AddSubgroup.zero_mem (principal_divisors G)⟩
