-- Prove2me | Theorems.Thm_C6BipartiteDomination_lemma_7_2_charge_values
-- name    : C6BipartiteDomination.lemma_7_2_charge_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:49:38.97275+00:00
-- url     : https://prove2.me/theorems/1f60d36d-e267-447b-a274-fb0cad35b772
-- title:
--   C6 Bipartite Domination: lemma 7 2 charge values
-- statement:
--   The C6 Bipartite Domination construction uses the lemma 7 2 charge values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A7.lean#L319-L336
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A7.lean#L319-L336

import Definitions.Def_C6BipartiteDomination_A6
import Definitions.Def_C6BipartiteDomination_A7
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.lemma_7_2_charge_values
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {w : V} (hw : w ∈ SPart G D)
    (ha : externalCharge G D w < 0) :
    (kCharge G D w = 3 ∧ betaCharge G D w = 2 ∧ externalCharge G D w = -7) ∨
    (kCharge G D w = 3 ∧ betaCharge G D w = 3 ∧ externalCharge G D w = -4) ∨
    (kCharge G D w = 4 ∧ betaCharge G D w = 2 ∧ externalCharge G D w = -14) := by sorry
