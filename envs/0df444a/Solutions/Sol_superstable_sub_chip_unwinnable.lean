-- Prove2me | solution 1 for superstable_sub_chip_unwinnable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:48:58.458798+00:00
-- url     : https://prove2.me/submissions/1dfd4f58-3180-44a9-9c1e-2e561c9e0c7b

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Config
public import Theorems.Thm_q_reduced_superstable_correspondence
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_effective_of_winnable_and_q_reduced
public import Theorems.Thm_legal_set_empty
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty



set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution {G : CFGraph} (q : G.V) (c : Config G q) :
  superstable G q c →
  ¬winnable G (c.chips - one_chip q) := by
  intro h_superstable
  let D := c.chips - one_chip q
  have h_red : q_reduced G q D := by
    apply (q_reduced_superstable_correspondence G q D).mpr
    refine ⟨c, h_superstable, ?_⟩
    -- Prove D = c - δ_q
    have h_deg_D : deg D = config_degree c - 1 := by
      dsimp only [D]
      exact deg_chips_sub_one_chip (c := c)
    rw [h_deg_D]
    dsimp only [D]
    exact (toDiv_config_degree_sub_one (c := c)).symm
  -- A winnable q-reduced divisor is effective, but D has -1 chips at q.
  intro h_winnable
  have h_nonneg_q := effective_of_winnable_and_q_reduced G q D h_winnable h_red q
  dsimp only [Pi.sub_apply, D] at h_nonneg_q
  simp only [c.q_zero, one_chip_apply_v, zero_sub, Int.reduceNeg, Int.neg_nonneg,
      Int.reduceLE] at h_nonneg_q
