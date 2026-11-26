-- Prove2me | Theorems.Thm_C6BipartiteDomination_coronaWitness_dominates
-- name    : C6BipartiteDomination.coronaWitness_dominates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:41:05.202194+00:00
-- url     : https://prove2.me/theorems/bfdc0ad6-8996-42d0-8915-d49ecf469a58
-- title:
--   C6 Bipartite Domination: corona Witness dominates
-- statement:
--   The C6 Bipartite Domination construction uses the corona Witness dominates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/Corona.lean#L59-L62
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/Corona.lean#L59-L62

import Definitions.Def_C6BipartiteDomination_Basic
import Mathlib.Tactic.FinCases
import Definitions.Def_C6BipartiteDomination_Corona
set_option autoImplicit true
open C6BipartiteDomination

theorem C6BipartiteDomination.coronaWitness_dominates : Dominates coronaGraph coronaWitness := by sorry
