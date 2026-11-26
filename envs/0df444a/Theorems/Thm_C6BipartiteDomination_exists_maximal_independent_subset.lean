-- Prove2me | Theorems.Thm_C6BipartiteDomination_exists_maximal_independent_subset
-- name    : C6BipartiteDomination.exists_maximal_independent_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:41:45.384095+00:00
-- url     : https://prove2.me/theorems/1ac685ff-2459-43a8-af15-1263f956ddad
-- title:
--   C6 Bipartite Domination: exists maximal independent subset
-- statement:
--   A cardinality-maximal independent subset of `A` is maximal by inclusion,
--   so it dominates every vertex of `A` that it does not contain.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A3.lean#L164-L201
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A3.lean#L164-L201

import Definitions.Def_C6BipartiteDomination_A2
import Definitions.Def_C6BipartiteDomination_A3
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.exists_maximal_independent_subset (A : Finset V) :
    ∃ I ⊆ A, Independent G I ∧
      ∀ ⦃a⦄, a ∈ A → a ∉ I → ∃ i ∈ I, G.Adj i a := by sorry
