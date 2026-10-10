-- Prove2me | Theorems.Thm_BookProof_ChapterPauliFundamental_lo_stepT
-- name    : BookProof.ChapterPauliFundamental.lo_stepT
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:29:30.924346+00:00
-- url     : https://prove2.me/theorems/c2f9a6ec-8120-47d5-be5a-61dc420ab241
-- title:
--   `BookProof.ChapterPauliFundamental.lo_stepT` : ∀ (μ : Fin 4) (T : Finset (Fin 4)), lo μ (stepT μ T) = lo μ T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliFundamental`.
--
--   `BookProof.ChapterPauliFundamental.lo_stepT` : ∀ (μ : Fin 4) (T : Finset (Fin 4)), lo μ (stepT μ T) = lo μ T
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliFundamental.lo_stepT`.

-- Generated from ChapterPauliFundamental.lean — theorem BookProof.ChapterPauliFundamental.lo_stepT
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterGammaCommutant
import Mathlib
import Definitions.Def_ChapterPauliFundamental
open BookProof.ChapterPauliFundamental


open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

theorem BookProof.ChapterPauliFundamental.lo_stepT : ∀ (μ : Fin 4) (T : Finset (Fin 4)), lo μ (stepT μ T) = lo μ T := by sorry
