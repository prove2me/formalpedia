-- Prove2me | Theorems.Thm_BookProof_ChapterPauliFundamental_G_orthogonal
-- name    : BookProof.ChapterPauliFundamental.G_orthogonal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:29:12.781651+00:00
-- url     : https://prove2.me/theorems/a90daf46-5ba1-450c-a8c6-4c01ed1bb0a9
-- title:
--   `BookProof.ChapterPauliFundamental.G_orthogonal` (T : Finset (Fin 4)) : G T * (G T)ᵀ = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliFundamental`.
--
--   `BookProof.ChapterPauliFundamental.G_orthogonal` (T : Finset (Fin 4)) : G T * (G T)ᵀ = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliFundamental.G_orthogonal`.

-- Generated from ChapterPauliFundamental.lean — theorem BookProof.ChapterPauliFundamental.G_orthogonal
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
import Mathlib
import Definitions.Def_ChapterPauliFundamental
open BookProof.ChapterPauliFundamental


open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

theorem BookProof.ChapterPauliFundamental.G_orthogonal (T : Finset (Fin 4)) : G T * (G T)ᵀ = 1 := by sorry
