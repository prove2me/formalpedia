-- Prove2me | Theorems.Thm_C6BipartiteDomination_lemma_6_1_charge_identity_of_counts
-- name    : C6BipartiteDomination.lemma_6_1_charge_identity_of_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:45:55.006553+00:00
-- url     : https://prove2.me/theorems/936a8f3b-eeb6-44df-82df-de50894d92fb
-- title:
--   C6 Bipartite Domination: lemma 6 1 charge identity of counts
-- statement:
--   Algebraic core of Lemma 6.1.  The two displayed hypotheses are the exact
--   partition and incidence equalities established by the structural lemmas of
--   this appendix; no graph-theoretic premise is folded into the arithmetic.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A6.lean#L191-L210
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A6.lean#L191-L210

import Definitions.Def_C6BipartiteDomination_A5
import Definitions.Def_C6BipartiteDomination_A6
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.lemma_6_1_charge_identity_of_counts
    (D : Finset V)
    (hWB : (WBPart G D).card =
      2 * (BPart G D).card +
        (∑ b ∈ BPart G D, xCharge G D b) + (SPart G D).card)
    (hInc : (∑ w ∈ SPart G D, betaCharge G D w) =
      ∑ b ∈ BPart G D, sCharge G D b) :
    8 * (WBPart G D).card - 7 * ((BPart G D).card + (Z0Part G D).card) =
      (∑ b ∈ BPart G D, vertexCharge G D b) +
        (∑ w ∈ SPart G D, externalCharge G D w) +
        7 * (incidenceTotal G D - (Z0Part G D).card) := by sorry
