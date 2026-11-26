-- Prove2me | Theorems.Thm_Auto_aux_discreteAverage_truncate_eq_of_mem
-- name    : Auto.aux_discreteAverage_truncate_eq_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:43:08.551948+00:00
-- url     : https://prove2.me/theorems/5bef7301-a573-4f23-a75c-45ac9c3bd90b
-- title:
--   Auto: aux discrete Average truncate eq of mem
-- statement:
--   Truncation to the sites relevant for a finite output set preserves all
--   averages whose scale does not exceed the chosen cutoff.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2185-L2195
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2185-L2195

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

theorem Auto.aux_discreteAverage_truncate_eq_of_mem {n : ℕ}
    {B : Finset (Fin n → ℕ)} {L N : ℕ} (hNL : N ≤ L)
    (F : Fin n → (Fin n → ℕ) → ℝ) {k : Fin n → ℕ} (hk : k ∈ B) :
    aux_discreteAverage N
        (fun i ↦ aux_truncate (aux_localInputSupport B L) (F i)) k =
      aux_discreteAverage N F k := by sorry
