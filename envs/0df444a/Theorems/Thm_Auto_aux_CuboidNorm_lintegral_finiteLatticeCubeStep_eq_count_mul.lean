-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_lintegral_finiteLatticeCubeStep_eq_count_mul
-- name    : Auto.aux_CuboidNorm.lintegral_finiteLatticeCubeStep_eq_count_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:41:53.674953+00:00
-- url     : https://prove2.me/theorems/c368dd8a-bc15-435e-9b46-6c9bdcc3c6ad
-- title:
--   aux Cuboid Norm: lintegral finite Lattice Cube Step eq count mul
-- statement:
--   The aux Cuboid Norm construction uses the lintegral finite Lattice Cube Step eq count mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1783-L1797
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1783-L1797

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Auto.aux_CuboidNorm
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]

theorem Auto.aux_CuboidNorm.lintegral_finiteLatticeCubeStep_eq_count_mul {n : ℕ}
    {ε : ℝ} (hε : ε ≤ 1) (A : Finset (ZVector n)) (a : ZVector n → ℝ)
    (hsupport : ∀ k, k ∉ A → a k = 0) (q : ℝ) (hq : 0 < q) :
    (∫⁻ x, ‖finiteLatticeCubeStep ε A a x‖ₑ ^ q ∂volume) =
      (∫⁻ k, ‖a k‖ₑ ^ q ∂Measure.count) *
        ∏ _ : Fin n, ENNReal.ofReal ε := by sorry
