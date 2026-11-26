-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11_pure_k3_charge_balance
-- name    : C6BipartiteDomination.paper11_pure_k3_charge_balance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:57:21.422852+00:00
-- url     : https://prove2.me/theorems/d0074fb8-35f9-4612-8080-f00e8c955d9f
-- title:
--   C6 Bipartite Domination: paper11 pure k3 charge balance
-- statement:
--   Numeric form of Lemma 11.1. It applies to any finite bipartite
--   incidence graph (hence to a pure `k=3` repair component): left degrees 1 and 2
--   carry debts at most 4 and 7; right degrees 1 and 2 carry resources at least
--   4 and 11. Connectivity is unnecessary for this stronger union statement.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L56-L153
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L56-L153

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem C6BipartiteDomination.paper11_pure_k3_charge_balance
    (L R : Finset V) (E : Finset (V × V))
    (hE : E ⊆ L.product R)
    (debt : V → ℤ) (resource : V → ℤ)
    (hLdegree : ∀ w ∈ L,
      paper11LeftDegree E R w = 1 ∨ paper11LeftDegree E R w = 2)
    (hRdegree : ∀ u ∈ R,
      paper11RightDegree E L u = 1 ∨ paper11RightDegree E L u = 2)
    (hDebt : ∀ w ∈ L,
      debt w ≤ if paper11LeftDegree E R w = 1 then 4 else 7)
    (hResource : ∀ u ∈ R,
      (if paper11RightDegree E L u = 1 then 4 else 11) ≤ resource u) :
    (∑ w ∈ L, debt w) ≤ ∑ u ∈ R, resource u := by sorry
