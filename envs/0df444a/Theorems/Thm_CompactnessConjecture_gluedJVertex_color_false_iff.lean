-- Prove2me | Theorems.Thm_CompactnessConjecture_gluedJVertex_color_false_iff
-- name    : CompactnessConjecture.gluedJVertex_color_false_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:37.072441+00:00
-- url     : https://prove2.me/theorems/ff984c82-13d7-4e1f-92ff-a25b3a8ca542
-- title:
--   CompactnessConjecture.gluedJVertex_color_false_iff
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

theorem CompactnessConjecture.gluedJVertex_color_false_iff
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hjoinFirst :
      G.Adj (copies 0 (.inl (.inl (0 : Fin 3)))) joining)
    (color : G.Coloring (Fin 2))
    (vertex : JVertex) :
    jColor vertex = false ↔
      color (gluedJVertex copies joining vertex) =
        color (copies 0 (.inl (.inl (0 : Fin 3)))) := by sorry
