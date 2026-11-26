-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_natToInt_eq_of_embedding
-- name    : Auto.aux_CuboidNorm.natToInt_eq_of_embedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:42:52.034992+00:00
-- url     : https://prove2.me/theorems/d3031059-aafc-59be-aacb-b876ce0eacea
-- title:
--   aux Cuboid Norm: nat To Int eq of embedding
-- statement:
--   The aux Cuboid Norm construction uses the nat To Int eq of embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2074-L2086
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2074-L2086

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

theorem Auto.aux_CuboidNorm.natToInt_eq_of_embedding {n : ℕ}
    (F : (Fin n → ℕ) → ℝ) (k : Fin n → ℕ) :
    aux_natToInt F (natToIntEmbedding k) = F k := by sorry
