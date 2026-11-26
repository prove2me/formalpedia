-- Prove2me | Theorems.Thm_BKAR_Forest_isSimplePath_of_edges_eq
-- name    : BKAR.Forest.isSimplePath_of_edges_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:02:15.06113+00:00
-- url     : https://prove2.me/theorems/1f2843df-b44a-44f6-8634-c7b8a95d42bf
-- title:
--   Forest: is Simple Path of edges eq
-- statement:
--   Simple paths are invariant under replacing the `Forest` representative data by another
--   forest with the same underlying edge set.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L669-L677
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L669-L677

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.isSimplePath_of_edges_eq
    (F G : Forest V) (hedges : F.edges = G.edges)
    {γ : List (Edge V)} {i j : V}
    (hγ : IsSimplePath F γ i j) :
    IsSimplePath G γ i j := by sorry
