-- Prove2me | Theorems.Thm_ErdosGirthChromatic_exists_girth_not_colorable
-- name    : ErdosGirthChromatic.exists_girth_not_colorable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:40:43.072776+00:00
-- url     : https://prove2.me/theorems/58e3621c-a649-4d7d-877d-950e4759df92
-- title:
--   Erdos Girth Chromatic: exists girth not colorable
-- statement:
--   For every `g` and `k`, for all sufficiently large `n` there is a graph on `n` vertices with
--   no cycle of length at most `g` that is not `k`-colourable.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Solution.lean#L46-L48
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Solution.lean#L46-L48

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirth
public import Definitions.Def_Mycielski_Family
public import Definitions.Def_FractionalLib_LarsenProppUllman
public import Definitions.Def_ErdosGirthChromatic_Solution
public import Theorems.Thm_ErdosGirth_exists_girth_not_colorable

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirthChromatic

theorem ErdosGirthChromatic.exists_girth_not_colorable (g k : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ G : SimpleGraph (Fin n), (g : ℕ∞) < G.egirth ∧ ¬ G.Colorable k := by sorry
