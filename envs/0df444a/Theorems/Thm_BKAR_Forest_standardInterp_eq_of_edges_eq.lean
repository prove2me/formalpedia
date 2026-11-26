-- Prove2me | Theorems.Thm_BKAR_Forest_standardInterp_eq_of_edges_eq
-- name    : BKAR.Forest.standardInterp_eq_of_edges_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:18:43.943451+00:00
-- url     : https://prove2.me/theorems/0acad853-8d18-484f-b3bd-8b7232ad6417
-- title:
--   Forest: standard Interp eq of edges eq
-- statement:
--   The standard BKAR interpolation point only depends on the underlying edge set
--   and the ambient edge-parameter values, not on the particular path data
--   stored in a `Forest`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L265-L284
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L265-L284

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.standardInterp_eq_of_edges_eq (F G : Forest V)
    (u : F.EdgeParam → ℝ) (v : G.EdgeParam → ℝ)
    (hedges : F.edges = G.edges)
    (hparam : ∀ e : Edge V, F.paramValue u e = G.paramValue v e) :
    F.standardInterp u = G.standardInterp v := by sorry
