-- Prove2me | Theorems.Thm_BookProof_ChapterPauliFundamental_sel_hi_insert
-- name    : BookProof.ChapterPauliFundamental.sel_hi_insert
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:28:27.321992+00:00
-- url     : https://prove2.me/theorems/c89cf2eb-d733-4b3b-a859-e9f2b2f8e70c
-- title:
--   `BookProof.ChapterPauliFundamental.sel_hi_insert` : ∀ (μ : Fin 4) (T : Finset (Fin 4)), μ ∉ T → sel (hi μ (insert μ T)) = μ :: sel (hi μ T)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliFundamental`.
--
--   `BookProof.ChapterPauliFundamental.sel_hi_insert` : ∀ (μ : Fin 4) (T : Finset (Fin 4)), μ ∉ T → sel (hi μ (insert μ T)) = μ :: sel (hi μ T)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliFundamental.sel_hi_insert`.

-- Generated from ChapterPauliFundamental.lean — theorem BookProof.ChapterPauliFundamental.sel_hi_insert
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
import Mathlib
import Definitions.Def_ChapterPauliFundamental
open BookProof.ChapterPauliFundamental


open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

theorem BookProof.ChapterPauliFundamental.sel_hi_insert : ∀ (μ : Fin 4) (T : Finset (Fin 4)), μ ∉ T →
    sel (hi μ (insert μ T)) = μ :: sel (hi μ T) := by sorry
