-- Prove2me | Theorems.Thm_C6BipartiteDomination_minimal_deficient_subset_bound
-- name    : C6BipartiteDomination.minimal_deficient_subset_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:41:45.993579+00:00
-- url     : https://prove2.me/theorems/72882ee0-45c1-4491-8c56-f3e96d144aca
-- title:
--   C6 Bipartite Domination: minimal deficient subset bound
-- statement:
--   The C6 Bipartite Domination construction uses the minimal deficient subset bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A3.lean#L203-L255
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A3.lean#L203-L255

import Definitions.Def_C6BipartiteDomination_A2
import Definitions.Def_C6BipartiteDomination_A3
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.minimal_deficient_subset_bound
    {X W S : Finset V}
    (hAcard : (neighborsIn G X W).card + 1 = X.card)
    (hmin : ∀ Y, Y ⊆ X → (neighborsIn G Y W).card < Y.card → X.card ≤ Y.card)
    (hS : S ⊆ neighborsIn G X W) (hSne : S.Nonempty) :
    (neighborsIn G S X).card ≥ S.card + 1 := by sorry
