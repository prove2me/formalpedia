-- Prove2me | solution 1 for maximal_unwinnable_symmetry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:57:55.427798+00:00
-- url     : https://prove2.me/submissions/34da57a2-c53e-4e50-bd63-b226e904d319

module
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
public import Definitions.Def_ChipFiringWithLean_RiemannRoch
public import Theorems.Thm_riemann_roch_for_graphs
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_degree_of_canonical_divisor
public import Theorems.Thm_maximal_unwinnable_deg
public import Theorems.Thm_rank_geq_iff
public import Theorems.Thm_rank_geq_neg_one
public import Theorems.Thm_rank_neg_one_iff_unwinnable
public import Theorems.Thm_rank_nonneg_iff_winnable
attribute [local simp] deg_one_chip



set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
universe u
open Multiset Finset
theorem _root_.solution
    {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G) :
  maximal_unwinnable G D ↔ maximal_unwinnable G (canonical_divisor G - D) := by
  set K := canonical_divisor G with K_def
  suffices ∀ (D : CFDiv G), maximal_unwinnable G D → maximal_unwinnable G (canonical_divisor G - D) by
    constructor
    exact this D
    intro h
    apply this (K-D) at h
    rw [sub_sub_self] at h
    exact h
  -- Now we can just prove the forward direction
  intro D h_max_unwin
  -- Get rank = -1 from maximal unwinnable
  have h_rank_neg : rank G D = -1 := by
    rw [rank_neg_one_iff_unwinnable]
    exact h_max_unwin.1

  -- Get degree = g-1 from maximal unwinnable
  have h_deg : deg D = genus G - 1 := maximal_unwinnable_deg h_conn D h_max_unwin

  -- Use Riemann-Roch
  have h_RR := riemann_roch_for_graphs h_conn D
  rw [h_rank_neg] at h_RR

  -- Get degree of K-D
  have h_deg_K := degree_of_canonical_divisor G
  have h_deg_KD : deg (canonical_divisor G - D) = genus G - 1 := by
    rw [deg.map_sub]
    rw [h_deg_K, h_deg]
    linarith

  constructor
  · -- K-D is unwinnable
    rw [←rank_neg_one_iff_unwinnable]
    linarith
  · -- Adding chip makes K-D winnable
    intro v -- Goal: winnable G ((K-D) + δᵥ)
    -- Let E = (K-D) + δᵥ
    set E : CFDiv G := (canonical_divisor G - D) + one_chip v with E_def
    suffices winnable G E by
      exact this
    -- To show E is winnable, we will use Riemann-Roch on E
    have h_deg_E : deg E = genus G := by
      rw [E_def, deg.map_add, deg_one_chip, h_deg_KD]
      linarith
    apply (rank_nonneg_iff_winnable G E).mp
    rw [rank_geq_iff G E]
    calc
      rank G E = rank G (K-E) + deg E +1 - genus G := by
        linarith [riemann_roch_for_graphs h_conn E]
      _ ≥ deg E - genus G := by
        linarith [rank_geq_neg_one G (K - E)]
      _ = 0 := by linarith[h_deg_E]
