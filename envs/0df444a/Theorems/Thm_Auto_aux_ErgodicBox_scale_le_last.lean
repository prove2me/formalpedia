-- Prove2me | Theorems.Thm_Auto_aux_ErgodicBox_scale_le_last
-- name    : Auto.aux_ErgodicBox.scale_le_last
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:44:41.512799+00:00
-- url     : https://prove2.me/theorems/bf30fccb-dfb1-51eb-a273-954c4dd0a58b
-- title:
--   aux Ergodic Box: scale le last
-- statement:
--   The last member of a strictly increasing finite scale tuple bounds all
--   of its scales.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2834-L2837
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2834-L2837

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
open Auto.aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators

theorem Auto.aux_ErgodicBox.scale_le_last {J : ℕ} (N : Fin (J + 1) → ℕ)
    (hN : StrictMono N) (q : Fin (J + 1)) :
    N q ≤ N (Fin.last J) := by sorry
