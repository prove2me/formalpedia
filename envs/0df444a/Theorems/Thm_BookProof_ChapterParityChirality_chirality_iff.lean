-- Prove2me | Theorems.Thm_BookProof_ChapterParityChirality_chirality_iff
-- name    : BookProof.ChapterParityChirality.chirality_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:06:03.746646+00:00
-- url     : https://prove2.me/theorems/c45ac95a-59b8-4781-b0df-564c226bb3eb
-- title:
--   `BookProof.ChapterParityChirality.chirality_iff` (v : Fin 2 × Fin 4 → ℂ) : isigma3 *ᵥ v = igamma5 *ᵥ v ↔ chi *ᵥ v = -v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterParityChirality`.
--
--   `BookProof.ChapterParityChirality.chirality_iff` (v : Fin 2 × Fin 4 → ℂ) : isigma3 *ᵥ v = igamma5 *ᵥ v ↔ chi *ᵥ v = -v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterParityChirality.chirality_iff`.

-- Generated from ChapterParityChirality.lean — theorem BookProof.ChapterParityChirality.chirality_iff
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterParity
import Definitions.Def_ChapterParitySU2
import Mathlib
import Definitions.Def_ChapterParityChirality
open BookProof.ChapterParityChirality


open Matrix
open scoped Kronecker


open BookProof.ChapterA3
open BookProof.ChapterParity
open BookProof.ChapterParitySU2

theorem BookProof.ChapterParityChirality.chirality_iff (v : Fin 2 × Fin 4 → ℂ) :
    isigma3 *ᵥ v = igamma5 *ᵥ v ↔ chi *ᵥ v = -v := by sorry
