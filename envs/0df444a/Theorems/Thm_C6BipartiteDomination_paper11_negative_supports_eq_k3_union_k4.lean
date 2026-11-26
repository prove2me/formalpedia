-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11_negative_supports_eq_k3_union_k4
-- name    : C6BipartiteDomination.paper11_negative_supports_eq_k3_union_k4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:01:28.004044+00:00
-- url     : https://prove2.me/theorems/1ec1597b-c869-41e0-9f77-8c11bff3761e
-- title:
--   C6 Bipartite Domination: paper11 negative supports eq k3 union k4
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 negative supports eq k3 union k4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L635-L653
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L635-L653

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11_negative_supports_eq_k3_union_k4 {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    paper11NegativeSupports G D =
      paper11K3Supports G D ∪ paper11K4Supports G D := by sorry
