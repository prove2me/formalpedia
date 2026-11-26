-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11K3_compensation_disjoint
-- name    : C6BipartiteDomination.paper11K3_compensation_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:04:39.847784+00:00
-- url     : https://prove2.me/theorems/eacfac67-7dc4-54c4-9919-23b05abaaea4
-- title:
--   C6 Bipartite Domination: paper11 K3 compensation disjoint
-- statement:
--   Compensation regions assigned to distinct selected vertices are
--   disjoint, as a consequence of the unique-owner lemma rather than an
--   assumption about the charge accounting.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L517-L535
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L517-L535

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11K3_compensation_disjoint {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u v : V}
    (hu : u ∈ BPart G D) (hv : v ∈ BPart G D) (hne : u ≠ v) :
    Disjoint (paper11K3Compensation G D hCan hmax u)
      (paper11K3Compensation G D hCan hmax v) := by sorry
