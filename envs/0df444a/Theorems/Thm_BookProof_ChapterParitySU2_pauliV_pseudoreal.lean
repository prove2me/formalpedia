-- Prove2me | Theorems.Thm_BookProof_ChapterParitySU2_pauliV_pseudoreal
-- name    : BookProof.ChapterParitySU2.pauliV_pseudoreal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:07:52.218235+00:00
-- url     : https://prove2.me/theorems/caeb5a20-da62-4e8a-9b2e-b264c9bcb9bb
-- title:
--   `BookProof.ChapterParitySU2.pauliV_pseudoreal` (j : Fin 3) : pauli2 * pauliV j * pauli2 = -((pauliV j).map (starRingEnd ℂ))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterParitySU2`.
--
--   `BookProof.ChapterParitySU2.pauliV_pseudoreal` (j : Fin 3) : pauli2 * pauliV j * pauli2 = -((pauliV j).map (starRingEnd ℂ))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterParitySU2.pauliV_pseudoreal`.

-- Generated from ChapterParitySU2.lean — theorem BookProof.ChapterParitySU2.pauliV_pseudoreal
import Mathlib
import Definitions.Def_ChapterParitySU2
import Definitions.Def_ChapterParity
open BookProof.ChapterParity
open BookProof.ChapterParitySU2


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterParity

theorem BookProof.ChapterParitySU2.pauliV_pseudoreal (j : Fin 3) :
    pauli2 * pauliV j * pauli2 = -((pauliV j).map (starRingEnd ℂ)) := by sorry
