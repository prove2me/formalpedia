-- Prove2me | Theorems.Thm_C6BipartiteDomination_responsibilityRegion_irreducible
-- name    : C6BipartiteDomination.responsibilityRegion_irreducible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:40:25.357293+00:00
-- url     : https://prove2.me/theorems/105ecf49-e4ec-5ad5-8fe8-d73d1f9c0b32
-- title:
--   C6 Bipartite Domination: responsibility Region irreducible
-- statement:
--   Lemma 2.3: every bipartite dominating set of the induced responsibility
--   region has at least `|X|` vertices. Together with the preceding witness
--   lemma, this gives the exact local optimum `γ_bip(G[R_D(X)]) = |X|`.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A2.lean#L90-L140
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A2.lean#L90-L140

import Definitions.Def_C6BipartiteDomination_Basic
import Definitions.Def_C6BipartiteDomination_A2
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.responsibilityRegion_irreducible
    {D X Y : Finset V}
    (hD : MinimumBipartiteDominatingSet G D)
    (hX : IsolatedSubset G D X)
    (hY : BipartiteDominatingOn G (responsibilityRegion G D X) Y) :
    X.card ≤ Y.card := by sorry
