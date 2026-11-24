-- Prove2me | solution 1 for rank_degree_inequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:55:54.869678+00:00
-- url     : https://prove2.me/submissions/084a519c-2ec2-4467-bc97-687733a5d25b

module
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Definitions.Def_ChipFiringWithLean_Rank
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
public import Theorems.Thm_moderator_symmetry
public import Theorems.Thm_moderator_degree
public import Theorems.Thm_unwinnable_of_moderator
public import Theorems.Thm_moderator_of_unwinnable
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
public import Theorems.Thm_linear_equiv_preserves_deg
public import Theorems.Thm_principal_iff_eq_prin
public import Theorems.Thm_rank_geq_iff
public import Theorems.Thm_rank_get_effective
public import Theorems.Thm_winnable_add_winnable
public import Theorems.Thm_winnable_equiv_winnable
public import Theorems.Thm_winnable_of_effective
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty



set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution
    {G : CFGraph} (h_conn : graph_connected G) (D : CFDiv G) :
    deg D - genus G < rank G D - rank G (canonical_divisor G - D) := by
  rcases rank_get_effective G D with ⟨E, E_eff, E_deg, D_E_unwin⟩
  rcases moderator_of_unwinnable h_conn (D - E) D_E_unwin with ⟨M, F, M_moderator, F_eff, M_equiv⟩
  set M' := canonical_divisor G - M with M'_eq
  have M'_moderator : is_moderator M' := moderator_symmetry M M_moderator

  set D' := canonical_divisor G - D with D'_eq
  have M'_equiv : linear_equiv G (D' - F + E) M' := by
    rw [M'_eq]
    dsimp only [linear_equiv, D']
    dsimp only [linear_equiv] at M_equiv
    rw [principal_iff_eq_prin] at M_equiv ⊢
    rcases M_equiv with ⟨σ, eq_σ⟩
    use σ
    rw [← eq_σ]
    abel

  have h_D'_F : ¬ winnable G (D' - F) := by
    by_contra!
    have := winnable_add_winnable G (D' - F) E this (winnable_of_effective G E E_eff)
    apply unwinnable_of_moderator M'_moderator
    apply winnable_equiv_winnable G (D' - F + E) M' this M'_equiv

  have ineq : deg F > rank G D' := by
      contrapose! h_D'_F
      apply (rank_geq_iff G D' (deg F)).mpr at h_D'_F
      dsimp only [rank_geq] at h_D'_F
      specialize h_D'_F F ⟨F_eff, rfl⟩
      exact h_D'_F

  -- Finally, degree calculations to finish the inequality
  have degF : deg F = - deg D + deg E + deg M := by
    rw [linear_equiv_preserves_deg G M (D - E + F) M_equiv]
    simp only [_root_.map_add, map_sub]
    linarith
  linarith [degF, moderator_degree M_moderator]
