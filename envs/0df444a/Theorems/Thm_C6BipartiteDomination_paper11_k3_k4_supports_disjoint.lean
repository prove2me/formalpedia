-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11_k3_k4_supports_disjoint
-- name    : C6BipartiteDomination.paper11_k3_k4_supports_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:00:27.820668+00:00
-- url     : https://prove2.me/theorems/a000d66b-15bc-5421-a9a5-01bb989e0d7d
-- title:
--   C6 Bipartite Domination: paper11 k3 k4 supports disjoint
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 k3 k4 supports disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L655-L661
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L655-L661

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11_k3_k4_supports_disjoint {D : Finset V} :
    Disjoint (paper11K3Supports G D) (paper11K4Supports G D) := by sorry
