-- Prove2me | Theorems.Thm_Erdos180_symplecticQuadrangle_adjacent_to_point
-- name    : Erdos180.symplecticQuadrangle_adjacent_to_point
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:03:08.590393+00:00
-- url     : https://prove2.me/theorems/233ced02-3107-4c16-aa6c-07e784e66c8f
-- title:
--   Neighbours of a point are lines through it
-- statement:
--   Every neighbour of a point $p$ in the incidence graph is a line $L$ with $p \le L$.
--
--   The incidence graph is bipartite with the point class and the line class as its sides;
--   this lemma is the form of that fact used when analysing where the two sides of a copy of
--   $S_k$ can land.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L1203-L1210

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem Erdos180.symplecticQuadrangle_adjacent_to_point
    {p : SymplecticPoint K} {v : QuadrangleVertex K}
    (h : (symplecticQuadrangle K).Adj (.inl p) v) :
    ∃ L : SymplecticLine K, v = .inr L ∧ p.1 ≤ L.1 := by sorry
