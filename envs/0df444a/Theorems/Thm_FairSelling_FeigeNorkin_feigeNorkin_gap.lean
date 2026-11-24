-- Prove2me | Theorems.Thm_FairSelling_FeigeNorkin_feigeNorkin_gap
-- name    : FairSelling.FeigeNorkin.feigeNorkin_gap
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:18:02.713107+00:00
-- url     : https://prove2.me/theorems/271e9ffe-111d-4fcd-b941-d2d11f68e586
-- title:
--   Feige Norkin: feige Norkin gap
-- statement:
--   **The Feige–Norkin gap, in real-valued form.**  For any three pairwise disjoint bundles,
--   one of the three agents receives at most `11/12` of the common target value `36`
--   (i.e. `11` out of `12` before the scaling by `3`).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkin.lean#L108-L125
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/FeigeNorkin.lean#L108-L125

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkin
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.FeigeNorkin

theorem FairSelling.FeigeNorkin.feigeNorkin_gap (A : Fin 3 → Finset (Fin 8))
    (hA : ∀ i k, i ≠ k → Disjoint (A i) (A k)) :
    (∑ g ∈ A 0, (fnR g : ℝ)) ≤ (11/12) * 36 ∨
    (∑ g ∈ A 1, (fnC g : ℝ)) ≤ (11/12) * 36 ∨
    (∑ g ∈ A 2, (fnU g : ℝ)) ≤ (11/12) * 36 := by sorry
