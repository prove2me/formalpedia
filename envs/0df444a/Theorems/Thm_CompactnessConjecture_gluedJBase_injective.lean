-- Prove2me | Theorems.Thm_CompactnessConjecture_gluedJBase_injective
-- name    : CompactnessConjecture.gluedJBase_injective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:36.289699+00:00
-- url     : https://prove2.me/theorems/73189eb1-0dfd-48d9-b158-a851c43b545e
-- title:
--   CompactnessConjecture.gluedJBase_injective
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

theorem CompactnessConjecture.gluedJBase_injective
    {G : SimpleGraph V}
    (copies : Fin 2 → SimpleGraph.Copy thetaGraph G)
    (hfirst :
      copies 1 (.inl (.inl (1 : Fin 3))) =
        copies 0 (.inl (.inl (1 : Fin 3))))
    (hsecond :
      copies 1 (.inl (.inl (2 : Fin 3))) =
        copies 0 (.inl (.inl (2 : Fin 3))))
    (hdistinct :
      copies 0 (.inl (.inl (0 : Fin 3))) ≠
        copies 1 (.inl (.inl (0 : Fin 3)))) :
    Function.Injective (gluedJBase copies) := by sorry
