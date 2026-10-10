-- Prove2me | Theorems.Thm_BookProof_ChapterPauliFundamental_sel_hi_mem
-- name    : BookProof.ChapterPauliFundamental.sel_hi_mem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:28:18.402746+00:00
-- url     : https://prove2.me/theorems/4d49c454-54c5-41b1-8c52-87a9a19f72f9
-- title:
--   `BookProof.ChapterPauliFundamental.sel_hi_mem` : ∀ (μ : Fin 4) (T : Finset (Fin 4)), μ ∈ T → sel (hi μ T) = μ :: sel (hi μ (T.erase μ))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliFundamental`.
--
--   `BookProof.ChapterPauliFundamental.sel_hi_mem` : ∀ (μ : Fin 4) (T : Finset (Fin 4)), μ ∈ T → sel (hi μ T) = μ :: sel (hi μ (T.erase μ))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliFundamental.sel_hi_mem`.

-- Generated from ChapterPauliFundamental.lean — theorem BookProof.ChapterPauliFundamental.sel_hi_mem
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
import Mathlib
import Definitions.Def_ChapterPauliFundamental
open BookProof.ChapterPauliFundamental


open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

theorem BookProof.ChapterPauliFundamental.sel_hi_mem : ∀ (μ : Fin 4) (T : Finset (Fin 4)), μ ∈ T →
    sel (hi μ T) = μ :: sel (hi μ (T.erase μ)) := by sorry
