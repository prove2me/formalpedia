-- Prove2me | Theorems.Thm_Auto_aux_fin_univ_nonempty
-- name    : Auto.aux_fin_univ_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:36:14.019336+00:00
-- url     : https://prove2.me/theorems/ca957cf8-4531-579d-b823-8ca8828c10e9
-- title:
--   Auto: aux fin univ nonempty
-- statement:
--   The Auto construction uses the aux fin univ nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L663-L665
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L663-L665

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

theorem Auto.aux_fin_univ_nonempty {n : ℕ} (hn : 0 < n) :
    (Finset.univ : Finset (Fin n)).Nonempty := by sorry
