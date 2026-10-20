-- Prove2me | Theorems.Thm_CompactnessConjecture_independentThetaTripleOrderedWitness_injective
-- name    : CompactnessConjecture.independentThetaTripleOrderedWitness_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:37.072441+00:00
-- url     : https://prove2.me/theorems/cb56104e-392d-4d14-812a-9cb611316b8c
-- title:
--   CompactnessConjecture.independentThetaTripleOrderedWitness_injective
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem CompactnessConjecture.independentThetaTripleOrderedWitness_injective
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G) :
    Function.Injective
      (independentThetaTripleOrderedWitness G hbip hfour hsix) := by sorry
