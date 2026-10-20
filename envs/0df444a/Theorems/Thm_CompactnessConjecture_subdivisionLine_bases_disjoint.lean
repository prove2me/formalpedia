-- Prove2me | Theorems.Thm_CompactnessConjecture_subdivisionLine_bases_disjoint
-- name    : CompactnessConjecture.subdivisionLine_bases_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:35.440987+00:00
-- url     : https://prove2.me/theorems/db846789-c9d9-4f12-a8ec-3a2232b4a90f
-- title:
--   CompactnessConjecture.subdivisionLine_bases_disjoint
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]

theorem CompactnessConjecture.subdivisionLine_bases_disjoint
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    (L : Fin 3 → SymplecticLine K)
    (C : Fin k → SymplecticLine K)
    (hbase : ∀ base : Fin 3,
      copy (.inl (.inl base)) = .inr (L base))
    (hcenter : ∀ center : Fin k,
      copy (.inl (.inr center)) = .inr (C center))
    {i j : Fin 3} (hij : i ≠ j) (center : Fin k) :
    Disjoint (L i).1 (L j).1 := by sorry
