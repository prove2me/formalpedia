-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_memLp_cuboidEmbed
-- name    : Auto.aux_CuboidNorm.memLp_cuboidEmbed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:41:24.796486+00:00
-- url     : https://prove2.me/theorems/9106b09a-ba4b-540a-926c-86532771f52f
-- title:
--   aux Cuboid Norm: mem Lp cuboid Embed
-- statement:
--   The aux Cuboid Norm construction uses the mem Lp cuboid Embed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1614-L1628
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1614-L1628

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

theorem Auto.aux_CuboidNorm.memLp_cuboidEmbed {n : ℕ}
    {ε δ : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1) (hεδ : ε + δ < 1)
    (i : Fin n) (A : Finset (ZVector n)) (a : ZVector n → ℝ)
    (hsupport : ∀ k, k ∉ A → a k = 0) (p : ℝ≥0∞)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    MemLp (aux_cuboidEmbed ε δ i a) p volume := by sorry
