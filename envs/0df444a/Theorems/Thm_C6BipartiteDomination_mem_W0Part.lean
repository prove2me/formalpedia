-- Prove2me | Theorems.Thm_C6BipartiteDomination_mem_W0Part
-- name    : C6BipartiteDomination.mem_W0Part
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:43:36.551809+00:00
-- url     : https://prove2.me/theorems/22d36c51-dc0b-4e31-bb98-5478c7ab6490
-- title:
--   C6 Bipartite Domination: mem W0 Part
-- statement:
--   The C6 Bipartite Domination construction uses the mem W0 Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A5.lean#L51-L54
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A5.lean#L51-L54

import Definitions.Def_C6BipartiteDomination_A4
import Definitions.Def_C6BipartiteDomination_A5
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.mem_W0Part (D : Finset V) (w : V) :
    w ∈ W0Part G D ↔ w ∉ D ∧ ∀ b ∈ BPart G D, ¬ G.Adj b w := by sorry
