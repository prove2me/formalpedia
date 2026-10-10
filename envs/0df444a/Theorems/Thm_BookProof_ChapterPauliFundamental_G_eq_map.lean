-- Prove2me | Theorems.Thm_BookProof_ChapterPauliFundamental_G_eq_map
-- name    : BookProof.ChapterPauliFundamental.G_eq_map
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:30:06.422005+00:00
-- url     : https://prove2.me/theorems/416ce6c7-0a71-4fd7-b3c3-f3e94d20032a
-- title:
--   `BookProof.ChapterPauliFundamental.G_eq_map` (T : Finset (Fin 4)) : G T = (GZ T).map (Int.cast)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliFundamental`.
--
--   `BookProof.ChapterPauliFundamental.G_eq_map` (T : Finset (Fin 4)) : G T = (GZ T).map (Int.cast)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliFundamental.G_eq_map`.

-- Generated from ChapterPauliFundamental.lean — theorem BookProof.ChapterPauliFundamental.G_eq_map
import Definitions.Def_ChapterGammaCommutant
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Definitions.Def_ChapterA3
open BookProof.ChapterA3
open BookProof.ChapterPauliFundamental


open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

theorem BookProof.ChapterPauliFundamental.G_eq_map (T : Finset (Fin 4)) : G T = (GZ T).map (Int.cast) := by sorry
