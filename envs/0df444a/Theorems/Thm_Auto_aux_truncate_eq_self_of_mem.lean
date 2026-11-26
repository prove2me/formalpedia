-- Prove2me | Theorems.Thm_Auto_aux_truncate_eq_self_of_mem
-- name    : Auto.aux_truncate_eq_self_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:42:59.807006+00:00
-- url     : https://prove2.me/theorems/da714fcc-b135-57af-9fb3-60bb76cd6efb
-- title:
--   Auto: aux truncate eq self of mem
-- statement:
--   The Auto construction uses the aux truncate eq self of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2156-L2160
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2156-L2160

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

theorem Auto.aux_truncate_eq_self_of_mem {n : ℕ}
    (A : Finset (Fin n → ℕ)) (F : (Fin n → ℕ) → ℝ)
    {k : Fin n → ℕ} (hk : k ∈ A) :
    aux_truncate A F k = F k := by sorry
