-- Prove2me | Theorems.Thm_C6BipartiteDomination_lemma_6_1_charge_identity
-- name    : C6BipartiteDomination.lemma_6_1_charge_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:47:52.032152+00:00
-- url     : https://prove2.me/theorems/c6351dc9-aa47-54fd-9cf6-06ef2210aae3
-- title:
--   C6 Bipartite Domination: lemma 6 1 charge identity
-- statement:
--   Lemma 6.1 in the paper: exact charge identity.  Its proof uses the
--   pairwise-disjoint private neighborhoods (from the secondary optimum), the
--   partition `W_B = P ⊔ S`, and double counting of `B`--`S` incidences.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A6.lean#L215-L222
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A6.lean#L215-L222

import Definitions.Def_C6BipartiteDomination_A5
import Definitions.Def_C6BipartiteDomination_A6
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.lemma_6_1_charge_identity
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D) :
    8 * (WBPart G D).card - 7 * ((BPart G D).card + (Z0Part G D).card) =
      (∑ b ∈ BPart G D, vertexCharge G D b) +
        (∑ w ∈ SPart G D, externalCharge G D w) +
        7 * (incidenceTotal G D - (Z0Part G D).card) := by sorry
