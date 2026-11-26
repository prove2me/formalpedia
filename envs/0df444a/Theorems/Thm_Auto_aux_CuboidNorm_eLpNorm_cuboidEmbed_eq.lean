-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_eLpNorm_cuboidEmbed_eq
-- name    : Auto.aux_CuboidNorm.eLpNorm_cuboidEmbed_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:41:03.048173+00:00
-- url     : https://prove2.me/theorems/72463636-74d8-5d80-9a6a-9b25664dda0e
-- title:
--   aux Cuboid Norm: e Lp Norm cuboid Embed eq
-- statement:
--   The aux Cuboid Norm construction uses the e Lp Norm cuboid Embed eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1556-L1567
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1556-L1567

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

theorem Auto.aux_CuboidNorm.eLpNorm_cuboidEmbed_eq {n : ℕ}
    {ε δ : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1) (hεδ : ε + δ < 1)
    (i : Fin n) (A : Finset (ZVector n)) (a : ZVector n → ℝ)
    (hsupport : ∀ k, k ∉ A → a k = 0) (p : ℝ≥0∞)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    eLpNorm (aux_cuboidEmbed ε δ i a) p volume =
      (∑ k ∈ A, ‖a k‖ₑ ^ p.toReal *
        ∏ j, ENNReal.ofReal (if j = i then δ else ε)) ^ (1 / p.toReal) := by sorry
