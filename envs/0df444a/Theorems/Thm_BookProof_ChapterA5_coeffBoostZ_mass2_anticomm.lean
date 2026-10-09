-- Prove2me | Theorems.Thm_BookProof_ChapterA5_coeffBoostZ_mass2_anticomm
-- name    : BookProof.ChapterA5.coeffBoostZ_mass2_anticomm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:12:31.741983+00:00
-- url     : https://prove2.me/theorems/5e644e8c-1dc2-4e4e-b9f9-249bce0c0e7e
-- title:
--   `BookProof.ChapterA5.coeffBoostZ_mass2_anticomm` (j : Fin 3) : coeffBoostZ j * coeffMass2Z + coeffMass2Z * coeffBoostZ j = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA5`.
--
--   `BookProof.ChapterA5.coeffBoostZ_mass2_anticomm` (j : Fin 3) : coeffBoostZ j * coeffMass2Z + coeffMass2Z * coeffBoostZ j = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA5.coeffBoostZ_mass2_anticomm`.

-- Generated from ChapterA5.lean — theorem BookProof.ChapterA5.coeffBoostZ_mass2_anticomm
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA5
open BookProof.ChapterA5


open Matrix


open BookProof.ChapterA3

theorem BookProof.ChapterA5.coeffBoostZ_mass2_anticomm (j : Fin 3) :
    coeffBoostZ j * coeffMass2Z + coeffMass2Z * coeffBoostZ j = 0 := by sorry
