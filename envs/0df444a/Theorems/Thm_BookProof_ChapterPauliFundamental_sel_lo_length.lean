-- Prove2me | Theorems.Thm_BookProof_ChapterPauliFundamental_sel_lo_length
-- name    : BookProof.ChapterPauliFundamental.sel_lo_length
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:28:36.122558+00:00
-- url     : https://prove2.me/theorems/a6d23a26-671d-458b-8f62-4c73ddea3b71
-- title:
--   `BookProof.ChapterPauliFundamental.sel_lo_length` : ∀ (μ : Fin 4) (T : Finset (Fin 4)), (sel (lo μ T)).length = (lo μ T).card
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliFundamental`.
--
--   `BookProof.ChapterPauliFundamental.sel_lo_length` : ∀ (μ : Fin 4) (T : Finset (Fin 4)), (sel (lo μ T)).length = (lo μ T).card
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliFundamental.sel_lo_length`.

-- Generated from ChapterPauliFundamental.lean — theorem BookProof.ChapterPauliFundamental.sel_lo_length
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
import Mathlib
import Definitions.Def_ChapterPauliFundamental
open BookProof.ChapterPauliFundamental


open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

theorem BookProof.ChapterPauliFundamental.sel_lo_length : ∀ (μ : Fin 4) (T : Finset (Fin 4)),
    (sel (lo μ T)).length = (lo μ T).card := by sorry
