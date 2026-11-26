-- Prove2me | Theorems.Thm_Auto_aux_mem_localInputSupport
-- name    : Auto.aux_mem_localInputSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:42:58.868848+00:00
-- url     : https://prove2.me/theorems/724f00f3-909c-4d35-916b-968c8ffc5ee3
-- title:
--   Auto: aux mem local Input Support
-- statement:
--   The Auto construction uses the aux mem local Input Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2147-L2154
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2147-L2154

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

theorem Auto.aux_mem_localInputSupport {n : ℕ}
    {B : Finset (Fin n → ℕ)} {L : ℕ} {k : Fin n → ℕ} (hk : k ∈ B)
    (i : Fin n) {m : ℕ} (hm : m < L) :
    k + aux_coordinate i m ∈ aux_localInputSupport B L := by sorry
