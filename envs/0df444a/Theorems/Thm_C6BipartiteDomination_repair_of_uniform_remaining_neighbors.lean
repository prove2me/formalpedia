-- Prove2me | Theorems.Thm_C6BipartiteDomination_repair_of_uniform_remaining_neighbors
-- name    : C6BipartiteDomination.repair_of_uniform_remaining_neighbors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:47:12.691334+00:00
-- url     : https://prove2.me/theorems/24225061-5192-41a3-b06a-fd8ea9042ee6
-- title:
--   C6 Bipartite Domination: repair of uniform remaining neighbors
-- statement:
--   The C6 Bipartite Domination construction uses the repair of uniform remaining neighbors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A8.lean#L87-L101
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A8.lean#L87-L101

import Definitions.Def_C6BipartiteDomination_A7
import Definitions.Def_C6BipartiteDomination_A8
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.repair_of_uniform_remaining_neighbors
    {D : Finset V} {w u : V}
    (hwD : w ∉ D) (hu : u ∈ BPart G D) (hwu : G.Adj w u)
    (c : V → Bool)
    (hc : ∀ ⦃x y⦄, x ∈ BPart G D → y ∈ BPart G D →
      G.Adj x y → c x ≠ c y)
    (c₀ : Bool)
    (huniform : ∀ v ∈ (BPart G D).erase u, G.Adj w v → c v = c₀) :
    IsRepairVertex G D w u := by sorry
