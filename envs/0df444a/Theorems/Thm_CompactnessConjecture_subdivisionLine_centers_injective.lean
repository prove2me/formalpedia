-- Prove2me | Theorems.Thm_CompactnessConjecture_subdivisionLine_centers_injective
-- name    : CompactnessConjecture.subdivisionLine_centers_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:35.440987+00:00
-- url     : https://prove2.me/theorems/db8f30d2-92b6-415e-afe4-9fd6bf744969
-- title:
--   CompactnessConjecture.subdivisionLine_centers_injective
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]

theorem CompactnessConjecture.subdivisionLine_centers_injective
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    (C : Fin k → SymplecticLine K)
    (hcenter : ∀ center : Fin k,
      copy (.inl (.inr center)) = .inr (C center)) :
    Function.Injective C := by sorry
