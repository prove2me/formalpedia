-- Prove2me | solution 1 for isVLDisjoint_posPart_sub_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:18:42.022359+00:00
-- url     : https://prove2.me/submissions/9cfb6d53-170c-41dd-82da-020a515bb98b

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Theorems.Thm_isVLDisjoint_posPart_negPart
public import Theorems.Thm_IsVLDisjoint_smul_right
public import Theorems.Thm_nonneg_smul_sup


set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
theorem _root_.solution (x y : X) {lam : ℝ} (hlam : 0 < lam) :
    IsVLDisjoint (x - lam • y)⁺ (y - lam⁻¹ • x)⁺ := by
  have hne : lam ≠ 0 := ne_of_gt hlam
  have hinv : (0 : ℝ) ≤ lam⁻¹ := le_of_lt (inv_pos.mpr hlam)
  have heq : (y - lam⁻¹ • x)⁺ = lam⁻¹ • (x - lam • y)⁻ := by
    rw [negPart_def, nonneg_smul_sup _ _ _ hinv, smul_zero, posPart_def,
        neg_sub, smul_sub, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [heq]
  exact (isVLDisjoint_posPart_negPart (x - lam • y)).smul_right lam⁻¹
