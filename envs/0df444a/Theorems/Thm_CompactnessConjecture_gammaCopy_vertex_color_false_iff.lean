-- Prove2me | Theorems.Thm_CompactnessConjecture_gammaCopy_vertex_color_false_iff
-- name    : CompactnessConjecture.gammaCopy_vertex_color_false_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:37.072441+00:00
-- url     : https://prove2.me/theorems/46385393-1b25-4309-9823-3f6515b7f33e
-- title:
--   CompactnessConjecture.gammaCopy_vertex_color_false_iff
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]

theorem CompactnessConjecture.gammaCopy_vertex_color_false_iff
    {G : SimpleGraph V}
    (color : G.Coloring (Fin 2))
    (witness : SimpleGraph.Copy gammaGraph G)
    (vertex : SubdivisionVertex 3) :
    subdivisionColor 3 vertex = false ↔
      color (witness vertex) = color (witness kSpecifiedCenter) := by sorry
