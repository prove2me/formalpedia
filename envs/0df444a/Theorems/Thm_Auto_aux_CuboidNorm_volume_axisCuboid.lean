-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_volume_axisCuboid
-- name    : Auto.aux_CuboidNorm.volume_axisCuboid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:40:51.958835+00:00
-- url     : https://prove2.me/theorems/1ec18891-c05f-564b-9561-8b827e1e020b
-- title:
--   aux Cuboid Norm: volume axis Cuboid
-- statement:
--   The aux Cuboid Norm construction uses the volume axis Cuboid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1329-L1337
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1329-L1337

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

theorem Auto.aux_CuboidNorm.volume_axisCuboid {n : ℕ} {ε δ : ℝ} (i : Fin n)
    (k : RVector n) :
    volume (axisCuboid ε δ i k) =
      ∏ j, ENNReal.ofReal (if j = i then δ else ε) := by sorry
