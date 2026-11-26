-- Prove2me | Theorems.Thm_C6BipartiteDomination_minimumOn_lift_toSubtype
-- name    : C6BipartiteDomination.minimumOn_lift_toSubtype
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:02:12.381808+00:00
-- url     : https://prove2.me/theorems/5e6bb12e-6f36-5537-90d6-2b4ca449b89b
-- title:
--   C6 Bipartite Domination: minimum On lift to Subtype
-- statement:
--   The C6 Bipartite Domination construction uses the minimum On lift to Subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/MainResults.lean#L93-L156
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/MainResults.lean#L93-L156

import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Definitions.Def_C6BipartiteDomination_MainResults
set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.minimumOn_lift_toSubtype {S E : Finset V}
    (hE : MinimumBipartiteDominatingOn G S E) :
    MinimumBipartiteDominatingSet (G.induce (S : Set V))
      (liftFinsetToSubtype S E hE.1.1) := by sorry
