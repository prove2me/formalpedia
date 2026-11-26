-- Prove2me | Theorems.Thm_C6BipartiteDomination_finite_graph_density_le_eight_fifteenths
-- name    : C6BipartiteDomination.finite_graph_density_le_eight_fifteenths
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T22:03:48.573828+00:00
-- url     : https://prove2.me/theorems/eb0a7248-8adb-40a9-b83e-11903b6505fe
-- title:
--   C6 Bipartite Domination: finite graph density le eight fifteenths
-- statement:
--   The C6 Bipartite Domination construction uses the finite graph density le eight fifteenths property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L338-L351
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L338-L351

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem C6BipartiteDomination.finite_graph_density_le_eight_fifteenths {H : FiniteSimpleGraphData}
    (hH : C6Admissible H) : finiteGraphDensity H ≤ (8 : ℝ) / 15 := by sorry
