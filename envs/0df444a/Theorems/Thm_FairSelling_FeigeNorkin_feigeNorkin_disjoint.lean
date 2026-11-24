-- Prove2me | Theorems.Thm_FairSelling_FeigeNorkin_feigeNorkin_disjoint
-- name    : FairSelling.FeigeNorkin.feigeNorkin_disjoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:47:03.987966+00:00
-- url     : https://prove2.me/theorems/aeafabb1-e654-4cbb-be98-57985618f337
-- title:
--   Feige Norkin: feige Norkin disjoint
-- statement:
--   Version of `feigeNorkin_core` for pairwise disjoint bundles: goods may also be left
--   unallocated (in the model with selling, sold).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkin.lean#L81-L103
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkin.lean#L81-L103

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkin
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.FeigeNorkin

theorem FairSelling.FeigeNorkin.feigeNorkin_disjoint (A : Fin 3 → Finset (Fin 8))
    (hA : ∀ i k, i ≠ k → Disjoint (A i) (A k)) :
    ∃ i : Fin 3, (∑ j ∈ A i, fnW i j) ≤ 33 := by sorry
