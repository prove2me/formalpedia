-- Prove2me | solution 1 for sum_sq_sum_le_sq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:35:55.415785+00:00
-- url     : https://prove2.me/submissions/3d5ae3b4-05aa-48df-b03b-6645bf361ccf

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Theorems.Thm_BSLambda_card_nbrs
public import Theorems.Thm_BSLambda_flipSet_apply_eq_self_iff
public import Theorems.Thm_BSLambda_flipSet_apply_of_mem
public import Theorems.Thm_BSLambda_flipSet_apply_of_notMem
public import Theorems.Thm_BSLambda_flipSet_empty
public import Theorems.Thm_BSLambda_flipSet_flipSet
public import Theorems.Thm_BSLambda_flipSet_left_inj
public import Theorems.Thm_BSLambda_flipSet_zeroInput_apply
public import Theorems.Thm_BSLambda_hammingDist_flipSet
public import Theorems.Thm_BSLambda_iterBlock_zero
public import Theorems.Thm_BSLambda_iterFun_zero
public import Theorems.Thm_BSLambda_sum_adj_row
public import Theorems.Thm_BSLambda_zeroInput_apply
attribute [local simp] BSLambda.card_nbrs
attribute [local simp] BSLambda.flipSet_apply_eq_self_iff
attribute [local simp] BSLambda.flipSet_apply_of_mem
attribute [local simp] BSLambda.flipSet_apply_of_notMem
attribute [local simp] BSLambda.flipSet_empty
attribute [local simp] BSLambda.flipSet_flipSet
attribute [local simp] BSLambda.flipSet_left_inj
attribute [local simp] BSLambda.flipSet_zeroInput_apply
attribute [local simp] BSLambda.hammingDist_flipSet
attribute [local simp] BSLambda.iterBlock_zero
attribute [local simp] BSLambda.iterFun_zero
attribute [local simp] BSLambda.sum_adj_row
attribute [local simp] BSLambda.zeroInput_apply



set_option autoImplicit true
@[expose] public section
public section
theorem _root_.solution {X Y : Type*} [Fintype X] [Fintype Y] (F : Y → X → ℝ) (t : Y → ℝ)
    (ht0 : ∀ y, 0 ≤ t y) (ht : ∀ y, ∑ x, F y x ^ 2 ≤ t y ^ 2) :
    ∑ x, (∑ y, F y x) ^ 2 ≤ (∑ y, t y) ^ 2 := by
  have hn (y : Y) : ‖(WithLp.toLp 2 (F y) : EuclideanSpace ℝ X)‖ ≤ t y := by
    refine (sq_le_sq₀ (norm_nonneg _) (ht0 y)).mp ?_
    rw [EuclideanSpace.norm_sq_eq]
    simpa [Real.norm_eq_abs, sq_abs] using ht y
  have key : ‖∑ y, (WithLp.toLp 2 (F y) : EuclideanSpace ℝ X)‖ ≤ ∑ y, t y :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ ↦ hn y)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) key 2
  rw [EuclideanSpace.norm_sq_eq] at hsq
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun x _ ↦ ?_)) hsq
  simp [Real.norm_eq_abs, sq_abs, Finset.sum_apply]
