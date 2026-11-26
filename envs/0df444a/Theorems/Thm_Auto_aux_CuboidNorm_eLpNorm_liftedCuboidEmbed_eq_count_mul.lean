-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_eLpNorm_liftedCuboidEmbed_eq_count_mul
-- name    : Auto.aux_CuboidNorm.eLpNorm_liftedCuboidEmbed_eq_count_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:41:25.846732+00:00
-- url     : https://prove2.me/theorems/1e5510ba-8571-599c-a5ab-679961f74199
-- title:
--   aux Cuboid Norm: e Lp Norm lifted Cuboid Embed eq count mul
-- statement:
--   The Euclidean cuboid lift has the corresponding counting norm times its
--   fixed box-volume factor.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1690-L1700
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1690-L1700

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

theorem Auto.aux_CuboidNorm.eLpNorm_liftedCuboidEmbed_eq_count_mul {n : ℕ}
    {ε δ : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1) (hεδ : ε + δ < 1)
    (i : Fin n) (A : Finset (ZVector n)) (a : ZVector n → ℝ)
    (hsupport : ∀ k, k ∉ A → a k = 0) (p : ℝ≥0∞)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    eLpNorm (aux_liftRaw (aux_cuboidEmbed ε δ i a)) p volume =
      eLpNorm a p Measure.count *
        (∏ j, ENNReal.ofReal (if j = i then δ else ε)) ^ (1 / p.toReal) := by sorry
