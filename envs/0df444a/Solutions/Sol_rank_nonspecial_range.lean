-- Prove2me | solution 1 for rank_nonspecial_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:58:40.176801+00:00
-- url     : https://prove2.me/submissions/27327b0d-3ba6-47f3-bdd5-3fbea08fa888

module
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
public import Definitions.Def_ChipFiringWithLean_RiemannRoch
public import Theorems.Thm_riemann_roch_for_graphs
public import Theorems.Thm_clifford_theorem
public import Theorems.Thm_degree_of_canonical_divisor
public import Theorems.Thm_rank_neg_one_of_deg_neg
public import Theorems.Thm_rank_neg_one_of_not_nonneg


set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
universe u
open Multiset Finset
theorem _root_.solution
  {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G) :
  -- Part 1
  (deg D < 0 → rank G D = -1) ∧
  -- Part 2
  (0 ≤ (deg D : ℚ) ∧ (deg D : ℚ) ≤ 2 * (genus G : ℚ) - 2 → (rank G D : ℚ) ≤ (deg D : ℚ) / 2) ∧
  -- Part 3
  (deg D > 2 * genus G - 2 → rank G D = deg D - genus G) := by
  constructor
  · -- Part 1: deg(D) < 0 implies r(D) = -1
    exact rank_neg_one_of_deg_neg G D

  constructor
  · -- Part 2: 0 ≤ deg(D) ≤ 2g-2 implies r(D) ≤ deg(D)/2
    intro ⟨h_deg_nonneg, h_deg_upper⟩
    by_cases h_rank : rank G D ≥ 0
    · -- Case where r(D) ≥ 0
      let K := canonical_divisor G
      by_cases h_rankKD : rank G (K - D) ≥ 0
      · -- Case where r(K-D) ≥ 0: use Clifford's theorem
        exact clifford_theorem h_conn D h_rank h_rankKD
      · -- Case where r(K-D) = -1: use Riemann-Roch
        have h_rr := riemann_roch_for_graphs h_conn D
        rw [rank_neg_one_of_not_nonneg G (K - D) h_rankKD] at h_rr
        -- So r(D) = deg D - g, which is at most deg D / 2 since deg D ≤ 2g - 2
        have h_rank_eq : rank G D = deg D - genus G := by linarith
        rw [h_rank_eq]
        push_cast
        linarith

    · -- Case where r(D) < 0
      rw [rank_neg_one_of_not_nonneg G D h_rank]
      push_cast
      linarith

  · -- Part 3: deg(D) > 2g-2 implies r(D) = deg(D) - g
    intro h_deg_large
    -- K-D has negative degree, hence rank -1
    have h_rankKD : rank G (canonical_divisor G - D) = -1 := by
      apply rank_neg_one_of_deg_neg
      rw [deg.map_sub, degree_of_canonical_divisor]
      linarith
    -- Apply Riemann-Roch to get r(D) = deg(D) - g
    have h_rr := riemann_roch_for_graphs h_conn D
    rw [h_rankKD] at h_rr
    linarith
