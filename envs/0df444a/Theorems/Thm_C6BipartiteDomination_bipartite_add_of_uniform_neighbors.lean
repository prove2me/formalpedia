-- Prove2me | Theorems.Thm_C6BipartiteDomination_bipartite_add_of_uniform_neighbors
-- name    : C6BipartiteDomination.bipartite_add_of_uniform_neighbors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:47:23.378844+00:00
-- url     : https://prove2.me/theorems/f4bb057e-cc23-485d-a764-b1e60dc6629d
-- title:
--   C6 Bipartite Domination: bipartite add of uniform neighbors
-- statement:
--   A fixed coloring of a bipartite base extends when all remaining neighbors
--   of the new vertex have one color.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A8.lean#L32-L61
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A8.lean#L32-L61

import Definitions.Def_C6BipartiteDomination_A7
import Definitions.Def_C6BipartiteDomination_A8
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.bipartite_add_of_uniform_neighbors
    {B S : Finset V} {w : V}
    (hSB : S ⊆ B) (hwS : w ∉ S)
    (c : V → Bool)
    (hc : ∀ ⦃u v⦄, u ∈ B → v ∈ B → G.Adj u v → c u ≠ c v)
    (c₀ : Bool)
    (huniform : ∀ v ∈ S, G.Adj w v → c v = c₀) :
    IsBipartiteOn G (S ∪ {w}) := by sorry
