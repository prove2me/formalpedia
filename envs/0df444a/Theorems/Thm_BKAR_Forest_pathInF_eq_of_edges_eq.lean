-- Prove2me | Theorems.Thm_BKAR_Forest_pathInF_eq_of_edges_eq
-- name    : BKAR.Forest.pathInF_eq_of_edges_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:03:27.085014+00:00
-- url     : https://prove2.me/theorems/a99cf20e-92c6-5128-ab6a-e46376cc3b6a
-- title:
--   Forest: path In F eq of edges eq
-- statement:
--   Canonical paths are invariant under changing only the `Forest` representative data, once
--   the underlying edge set is fixed.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L698-L705
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Forest.lean#L698-L705

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

theorem BKAR.Forest.pathInF_eq_of_edges_eq
    (F G : Forest V) (hedges : F.edges = G.edges)
    {i j : V} (hF : F.inSameComponent i j)
    (hG : G.inSameComponent i j) :
    F.pathInF i j hF = G.pathInF i j hG := by sorry
