-- Prove2me | Theorems.Thm_Conway99Formal_CubicOperators_Graph_incident_sum_of_incidence_square
-- name    : Conway99Formal.CubicOperators.Graph.incident_sum_of_incidence_square
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T06:45:00.211354+00:00
-- url     : https://prove2.me/theorems/cb87fcf5-c852-4791-b1a1-f4b6bb8ec8f5
-- title:
--   Incident sum of incidence square
-- statement:
--   For a finite graph with a point frame and the stated incidence-matrix square identity, the incident triangle-vector sum equals the selected point-frame column.
-- source:
--   blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/cubic-operators/CubicOperators.lean#L401-L448

import Definitions.Def_CubicOperators
import Mathlib

namespace Conway99Formal.CubicOperators.Graph
end Conway99Formal.CubicOperators.Graph

set_option autoImplicit false

/-! Algebraic contraction lemmas for the graph-owned triangle cubic. The
incidence identities in the hypotheses are the explicit graph bridge. -/

open Conway99Formal.CubicOperators

open Finset

variable {T I : Type*} [Fintype T] [Fintype I]






























































open Conway99Formal.CubicOperators.Graph

open Finset



variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem Conway99Formal.CubicOperators.Graph.incident_sum_of_incidence_square (Pi : Matrix Coord V ℝ)
    (hf : IsPointFrame G Pi)
    (hinc : realIncidenceMatrix G * (realIncidenceMatrix G).transpose =
      7 • (1 : Matrix V V ℝ) + G.adjMatrix ℝ)
    (u : V) (i : Coord) :
    (∑ T : Triangle G, incidence G u T * triangleVector G Pi T i) =
      pointColumn Pi u i := by sorry
