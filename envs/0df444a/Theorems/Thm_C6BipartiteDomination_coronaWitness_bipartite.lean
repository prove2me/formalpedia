-- Prove2me | Theorems.Thm_C6BipartiteDomination_coronaWitness_bipartite
-- name    : C6BipartiteDomination.coronaWitness_bipartite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:40:55.684326+00:00
-- url     : https://prove2.me/theorems/ef8fb96f-2992-44de-9875-f17f777ef00b
-- title:
--   C6 Bipartite Domination: corona Witness bipartite
-- statement:
--   The C6 Bipartite Domination construction uses the corona Witness bipartite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/Corona.lean#L66-L70
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/Corona.lean#L66-L70

import Definitions.Def_C6BipartiteDomination_Basic
import Mathlib.Tactic.FinCases
import Definitions.Def_C6BipartiteDomination_Corona
set_option autoImplicit true
open C6BipartiteDomination
set_option maxHeartbeats 1000000

theorem C6BipartiteDomination.coronaWitness_bipartite : IsBipartiteOn coronaGraph coronaWitness := by sorry
