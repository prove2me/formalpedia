-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11_nonnegative_charge_partition
-- name    : C6BipartiteDomination.paper11_nonnegative_charge_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:00:37.141183+00:00
-- url     : https://prove2.me/theorems/fc18308a-3509-5868-a11b-e62123bfa8d2
-- title:
--   C6 Bipartite Domination: paper11 nonnegative charge partition
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 nonnegative charge partition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L687-L705
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L687-L705

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11_nonnegative_charge_partition {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    SPart G D = paper11NegativeSupports G D ∪
      paper11NonnegativeSupports G D := by sorry
