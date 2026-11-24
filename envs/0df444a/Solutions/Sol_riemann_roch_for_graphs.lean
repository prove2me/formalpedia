-- Prove2me | solution 1 for riemann_roch_for_graphs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:57:00.615992+00:00
-- url     : https://prove2.me/submissions/849373bd-3d69-404c-937d-5b27bd56a806

module
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
public import Definitions.Def_ChipFiringWithLean_RiemannRoch
public import Theorems.Thm_degree_of_canonical_divisor
public import Theorems.Thm_rank_degree_inequality


set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
universe u
open Multiset Finset
theorem _root_.solution {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G) :
  rank G D - rank G (canonical_divisor G - D) = deg D - genus G + 1 := by
  set K := canonical_divisor G with K_eq
  have h_ineq := rank_degree_inequality h_conn D
  have h_ineq_rev : deg (K-D) - genus G < rank G (K-D) - rank G D := by
    convert rank_degree_inequality h_conn (K-D)
    abel
  have deg_sub : deg (K-D) = deg K - deg D := by rw [deg.map_sub]
  have h_deg_K : deg (canonical_divisor G) = 2 * genus G - 2 := degree_of_canonical_divisor G
  linarith
