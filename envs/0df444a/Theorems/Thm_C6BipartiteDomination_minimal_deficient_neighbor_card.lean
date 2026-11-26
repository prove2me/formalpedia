-- Prove2me | Theorems.Thm_C6BipartiteDomination_minimal_deficient_neighbor_card
-- name    : C6BipartiteDomination.minimal_deficient_neighbor_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:41:32.009717+00:00
-- url     : https://prove2.me/theorems/6d1b3fea-2919-52b6-84fb-2a6adcc7f832
-- title:
--   C6 Bipartite Domination: minimal deficient neighbor card
-- statement:
--   The C6 Bipartite Domination construction uses the minimal deficient neighbor card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A3.lean#L138-L160
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A3.lean#L138-L160

import Definitions.Def_C6BipartiteDomination_A2
import Definitions.Def_C6BipartiteDomination_A3
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.minimal_deficient_neighbor_card
    {X W : Finset V}
    (hXne : X.Nonempty)
    (hdef : (neighborsIn G X W).card < X.card)
    (hmin : ∀ Y, Y ⊆ X → (neighborsIn G Y W).card < Y.card → X.card ≤ Y.card) :
    (neighborsIn G X W).card + 1 = X.card := by sorry
