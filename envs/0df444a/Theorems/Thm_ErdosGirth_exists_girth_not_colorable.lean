-- Prove2me | Theorems.Thm_ErdosGirth_exists_girth_not_colorable
-- name    : ErdosGirth.exists_girth_not_colorable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:29:22.873991+00:00
-- url     : https://prove2.me/theorems/aaedb0e5-11e4-495e-9e4f-1cd60ca9e00d
-- title:
--   Erdos Girth: exists girth not colorable
-- statement:
--   For every `g` and `k`, for all sufficiently large `n` there is a graph on `n` vertices with
--   no cycle of length at most `g` that is not `k`-colourable.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirth.lean#L51-L78
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirth.lean#L51-L78

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
public import Definitions.Def_GirthLib_ErdosGirth
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth

theorem ErdosGirth.exists_girth_not_colorable (g k : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ G : SimpleGraph (Fin n), (g : ℕ∞) < G.egirth ∧ ¬ G.Colorable k := by sorry
