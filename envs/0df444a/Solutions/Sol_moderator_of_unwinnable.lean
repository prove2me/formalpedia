-- Prove2me | solution 1 for moderator_of_unwinnable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:54:35.829795+00:00
-- url     : https://prove2.me/submissions/58f1a710-0aed-4b34-97cb-b9114c4648e8

module
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Definitions.Def_ChipFiringWithLean_Rank
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
public import Theorems.Thm_superstable_of_divisor
public import Theorems.Thm_superstable_of_divisor_negative_k
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_eff_one_chip
public import Theorems.Thm_legal_set_empty
public import Theorems.Thm_maximal_superstable_exists
public import Theorems.Thm_maximal_superstable_orientation
public import Theorems.Thm_principal_iff_eq_prin
public import Theorems.Thm_sub_eff_iff_geq
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty



set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution {G : CFGraph} (h_conn: graph_connected G) (D : CFDiv G) (unwin : ¬ winnable G D) :
  ∃ (M H : CFDiv G), is_moderator M ∧ effective H ∧ linear_equiv G M (D+H) := by
  let q := Classical.arbitrary G.V
  rcases superstable_of_divisor h_conn q D with ⟨c, k, h_equiv, h_super⟩
  have h_k_neg : k < 0 := superstable_of_divisor_negative_k G q D unwin c k h_equiv h_super
  rcases maximal_superstable_exists G q c h_super with ⟨c', h_max', h_ge⟩
  rcases maximal_superstable_orientation G q c' h_max' with ⟨O, hO, h_orient_eq_c'⟩
  let H : CFDiv G := -(k+1) • (one_chip q) + c'.chips - c.chips
  have h_H_eff : effective H := by
    have diff_eff : effective (c'.chips - c.chips) := by
      rwa [sub_eff_iff_geq]
    have src_eff : effective (-(k+1) • one_chip q)  := by
      intro v
      rw [Pi.smul_apply, smul_eq_mul]
      apply mul_nonneg
      · -- Prove -(k + 1) ≥ 0
        linarith [h_k_neg]
      · -- Prove one_chip q v ≥ 0
        exact eff_one_chip q v
    have := (Eff G).add_mem src_eff diff_eff
    rwa [← add_sub_assoc] at this
  let M := c'.chips - one_chip q
  have M_eq : linear_equiv G M (D + H) := by
    simp only [linear_equiv, principal_iff_eq_prin, H, M] at ⊢ h_equiv
    rcases h_equiv with ⟨σ, eq_σ⟩
    use (-σ)
    rw [map_neg, ← eq_σ]
    funext v; simp only [neg_add_rev, Int.reduceNeg, zsmul_eq_mul, Int.cast_add, Int.cast_neg,
        Int.cast_one, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.neg_apply, Pi.one_apply,
        Pi.intCast_apply, Int.cast_eq, neg_sub]; ring

  have h_M_O : M = ordiv G O := by
    have c'_eq : c' = toConfig (orqed O hO) := by
      rw [← h_orient_eq_c']
      exact config_and_divisor_from_O O hO

    have : toDiv (genus G - 1) (toConfig (orqed O hO)) = ordiv G O := by
      calc
        toDiv (genus G - 1) (toConfig (orqed O hO))
            = toDiv (deg (orqed O hO).D) (toConfig (orqed O hO)) := by
                have h_deg_orqed : deg (orqed O hO).D = genus G - 1 := by
                  simpa only [orqed] using degree_ordiv O
                rw [h_deg_orqed]
        _ = (orqed O hO).D := div_of_config_of_div (orqed O hO)
        _ = ordiv G O := rfl
    rw [← this]
    dsimp only [toDiv, M]
    rw [c'_eq]
    have : (genus G - 1 - config_degree (toConfig (orqed O hO))) = -1 := by
      have h_cfg_deg : config_degree (toConfig (orqed O hO)) = genus G := by
        rw [← config_and_divisor_from_O O hO]
        exact config_degree_from_O O hO
      rw [h_cfg_deg]
      ring
    simp only [this, Int.reduceNeg, neg_smul, one_smul]
    rw [sub_eq_add_neg]
  have h_M_moderator : is_moderator M := by
    exact ⟨O, ⟨hO.1, h_M_O⟩⟩
  use M, H
