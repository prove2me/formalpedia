-- Prove2me | Theorems.Thm_CompactnessConjecture_gamma_bad_triple_fiber_mass_le_two_orderedTheta
-- name    : CompactnessConjecture.gamma_bad_triple_fiber_mass_le_two_orderedTheta
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:37.072441+00:00
-- url     : https://prove2.me/theorems/d8cf521c-6a0c-4535-9455-5c61187f4d94
-- title:
--   CompactnessConjecture.gamma_bad_triple_fiber_mass_le_two_orderedTheta
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem CompactnessConjecture.gamma_bad_triple_fiber_mass_le_two_orderedTheta
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hbip : host.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free host)
    (hsix : (SimpleGraph.cycleGraph 6).Free host) :
    finiteBadFiberMass
        (fun triple : IndependentThetaTriple host =>
          commonCenterFinset host triple.val)
        (GammaGood host) ≤
      2 * orderedThetaTripleCount host := by sorry
