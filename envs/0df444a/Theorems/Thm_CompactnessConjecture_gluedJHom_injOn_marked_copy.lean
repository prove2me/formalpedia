-- Prove2me | Theorems.Thm_CompactnessConjecture_gluedJHom_injOn_marked_copy
-- name    : CompactnessConjecture.gluedJHom_injOn_marked_copy
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:36.289699+00:00
-- url     : https://prove2.me/theorems/be804b49-d43d-48a8-a010-b7a116022e1a
-- title:
--   CompactnessConjecture.gluedJHom_injOn_marked_copy
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

theorem CompactnessConjecture.gluedJHom_injOn_marked_copy
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (joining : V)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (hjoinFirst :
      G.Adj (copies 0 (.inl (.inl (0 : Fin 3)))) joining)
    (hjoinSecond :
      G.Adj (copies 1 (.inl (.inl (0 : Fin 3)))) joining)
    (copy : Fin 2) :
    Set.InjOn
      (gluedJHom copies joining hfirst hsecond
        hjoinFirst hjoinSecond)
      {vertex | InJCopy copy vertex} := by sorry
