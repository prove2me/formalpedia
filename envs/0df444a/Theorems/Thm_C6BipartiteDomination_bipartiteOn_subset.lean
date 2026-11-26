-- Prove2me | Theorems.Thm_C6BipartiteDomination_bipartiteOn_subset
-- name    : C6BipartiteDomination.bipartiteOn_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:42:15.308194+00:00
-- url     : https://prove2.me/theorems/fb760c91-4edf-54fc-92fc-3b71d3a701f4
-- title:
--   C6 Bipartite Domination: bipartite On subset
-- statement:
--   The C6 Bipartite Domination construction uses the bipartite On subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A4.lean#L92-L95
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A4.lean#L92-L95

import Definitions.Def_C6BipartiteDomination_A3
import Definitions.Def_C6BipartiteDomination_A4
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.bipartiteOn_subset {D E : Finset V} (hE : E ⊆ D)
    (hD : IsBipartiteOn G D) : IsBipartiteOn G E := by sorry
