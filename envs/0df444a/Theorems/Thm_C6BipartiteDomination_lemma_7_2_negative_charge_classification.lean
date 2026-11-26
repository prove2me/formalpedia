-- Prove2me | Theorems.Thm_C6BipartiteDomination_lemma_7_2_negative_charge_classification
-- name    : C6BipartiteDomination.lemma_7_2_negative_charge_classification
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:46:57.103474+00:00
-- url     : https://prove2.me/theorems/ae0f9574-dcba-5b2e-b59c-5cf0bb780c28
-- title:
--   C6 Bipartite Domination: lemma 7 2 negative charge classification
-- statement:
--   Lemma 7.2: under the maximum-degree-six hypothesis, a negative external
--   charge has exactly one of the three paper-listed `(k, β)` types.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A7.lean#L294-L317
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A7.lean#L294-L317

import Definitions.Def_C6BipartiteDomination_A6
import Definitions.Def_C6BipartiteDomination_A7
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.lemma_7_2_negative_charge_classification
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {w : V} (hw : w ∈ SPart G D)
    (ha : externalCharge G D w < 0) :
    (kCharge G D w = 3 ∧ betaCharge G D w = 2) ∨
    (kCharge G D w = 3 ∧ betaCharge G D w = 3) ∨
    (kCharge G D w = 4 ∧ betaCharge G D w = 2) := by sorry
