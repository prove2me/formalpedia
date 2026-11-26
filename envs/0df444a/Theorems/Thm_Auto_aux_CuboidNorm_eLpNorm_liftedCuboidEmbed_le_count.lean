-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_eLpNorm_liftedCuboidEmbed_le_count
-- name    : Auto.aux_CuboidNorm.eLpNorm_liftedCuboidEmbed_le_count
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:41:35.954189+00:00
-- url     : https://prove2.me/theorems/0ba3b86f-e65f-529a-bbdf-a53fd471b1b6
-- title:
--   aux Cuboid Norm: e Lp Norm lifted Cuboid Embed le count
-- statement:
--   The aux Cuboid Norm construction uses the e Lp Norm lifted Cuboid Embed le count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1714-L1731
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1714-L1731

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

theorem Auto.aux_CuboidNorm.eLpNorm_liftedCuboidEmbed_le_count {n : ℕ}
    {ε δ : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1) (hεδ : ε + δ < 1)
    (i : Fin n) (A : Finset (ZVector n)) (a : ZVector n → ℝ)
    (hsupport : ∀ k, k ∉ A → a k = 0) (p : ℝ≥0∞)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞)
    (hvolume : ∏ j, ENNReal.ofReal (if j = i then δ else ε) ≤ 1) :
    eLpNorm (aux_liftRaw (aux_cuboidEmbed ε δ i a)) p volume ≤
      eLpNorm a p Measure.count := by sorry
