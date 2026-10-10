-- Prove2me | Theorems.Thm_BookProof_ChapterParityChirality_chirality_iff_proj
-- name    : BookProof.ChapterParityChirality.chirality_iff_proj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:06:58.43881+00:00
-- url     : https://prove2.me/theorems/63ed0005-c7a5-47b2-91f8-37c3f37dbfeb
-- title:
--   `BookProof.ChapterParityChirality.chirality_iff_proj` (v : Fin 2 × Fin 4 → ℂ) : chi *ᵥ v = -v ↔ QLProj *ᵥ v = v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterParityChirality`.
--
--   `BookProof.ChapterParityChirality.chirality_iff_proj` (v : Fin 2 × Fin 4 → ℂ) : chi *ᵥ v = -v ↔ QLProj *ᵥ v = v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterParityChirality.chirality_iff_proj`.

-- Generated from ChapterParityChirality.lean — theorem BookProof.ChapterParityChirality.chirality_iff_proj
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

theorem BookProof.ChapterParityChirality.chirality_iff_proj (v : Fin 2 × Fin 4 → ℂ) :
    chi *ᵥ v = -v ↔ QLProj *ᵥ v = v := by sorry
