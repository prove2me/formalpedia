-- Prove2me | Theorems.Thm_C6BipartiteDomination_degreeTo_as_sum
-- name    : C6BipartiteDomination.degreeTo_as_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:45:19.22031+00:00
-- url     : https://prove2.me/theorems/5c604e22-9174-4fa9-86f3-3b7ffa9617e8
-- title:
--   C6 Bipartite Domination: degree To as sum
-- statement:
--   The C6 Bipartite Domination construction uses the degree To as sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A6.lean#L25-L29
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A6.lean#L25-L29

import Definitions.Def_C6BipartiteDomination_A5
import Definitions.Def_C6BipartiteDomination_A6
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
open Classical

theorem C6BipartiteDomination.degreeTo_as_sum (A : Finset V) (v : V) :
    degreeTo G A v = ∑ u ∈ A, if G.Adj v u then 1 else 0 := by sorry
