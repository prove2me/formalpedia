-- Prove2me | Theorems.Thm_BookProof_ChapterPauliFundamental_gp_append
-- name    : BookProof.ChapterPauliFundamental.gp_append
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:27:59.615979+00:00
-- url     : https://prove2.me/theorems/323aceab-ddbf-4596-b200-fb87a700a2b5
-- title:
--   `BookProof.ChapterPauliFundamental.gp_append` (A : Fin 4 → M4) (l₁ l₂ : List (Fin 4)) : gp A (l₁ ++ l₂) = gp A l₁ * gp A l₂
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliFundamental`.
--
--   `BookProof.ChapterPauliFundamental.gp_append` (A : Fin 4 → M4) (l₁ l₂ : List (Fin 4)) : gp A (l₁ ++ l₂) = gp A l₁ * gp A l₂
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliFundamental.gp_append`.

-- Generated from ChapterPauliFundamental.lean — theorem BookProof.ChapterPauliFundamental.gp_append
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
import Mathlib
import Definitions.Def_ChapterPauliFundamental
open BookProof.ChapterPauliFundamental


open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

theorem BookProof.ChapterPauliFundamental.gp_append (A : Fin 4 → M4) (l₁ l₂ : List (Fin 4)) :
    gp A (l₁ ++ l₂) = gp A l₁ * gp A l₂ := by sorry
