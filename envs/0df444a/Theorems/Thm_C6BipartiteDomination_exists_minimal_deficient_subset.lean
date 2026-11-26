-- Prove2me | Theorems.Thm_C6BipartiteDomination_exists_minimal_deficient_subset
-- name    : C6BipartiteDomination.exists_minimal_deficient_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:41:35.949191+00:00
-- url     : https://prove2.me/theorems/ee71ea12-4796-4aec-b2ab-c9f5d755c4e5
-- title:
--   C6 Bipartite Domination: exists minimal deficient subset
-- statement:
--   The C6 Bipartite Domination construction uses the exists minimal deficient subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A3.lean#L91-L111
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A3.lean#L91-L111

import Definitions.Def_C6BipartiteDomination_A2
import Definitions.Def_C6BipartiteDomination_A3
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.exists_minimal_deficient_subset
    (D W : Finset V) (hCover : neighborsIn G D W = W)
    (hlarge : W.card < D.card) :
    ∃ X ∈ D.powerset,
      (neighborsIn G X W).card < X.card ∧
      ∀ Y, Y ⊆ X → (neighborsIn G Y W).card < Y.card → X.card ≤ Y.card := by sorry
