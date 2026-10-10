-- Prove2me | Theorems.Thm_BookProof_ChapterParitySU2_su2_conj_inner
-- name    : BookProof.ChapterParitySU2.su2_conj_inner
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:08:00.692761+00:00
-- url     : https://prove2.me/theorems/b7624f67-a624-46ed-9359-568472d529e3
-- title:
--   `BookProof.ChapterParitySU2.su2_conj_inner` (j : Fin 3) : (su2gen j).map (starRingEnd ℂ) = pauli2 * su2gen j * pauli2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterParitySU2`.
--
--   `BookProof.ChapterParitySU2.su2_conj_inner` (j : Fin 3) : (su2gen j).map (starRingEnd ℂ) = pauli2 * su2gen j * pauli2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterParitySU2.su2_conj_inner`.

-- Generated from ChapterParitySU2.lean — theorem BookProof.ChapterParitySU2.su2_conj_inner
import Mathlib
import Definitions.Def_ChapterParitySU2
import Definitions.Def_ChapterParity
open BookProof.ChapterParity
open BookProof.ChapterParitySU2


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterParity

theorem BookProof.ChapterParitySU2.su2_conj_inner (j : Fin 3) :
    (su2gen j).map (starRingEnd ℂ) = pauli2 * su2gen j * pauli2 := by sorry
