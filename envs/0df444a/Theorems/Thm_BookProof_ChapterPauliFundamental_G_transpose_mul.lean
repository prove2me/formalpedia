-- Prove2me | Theorems.Thm_BookProof_ChapterPauliFundamental_G_transpose_mul
-- name    : BookProof.ChapterPauliFundamental.G_transpose_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:30:20.467135+00:00
-- url     : https://prove2.me/theorems/dea643cf-c1a5-4abc-934f-ae22fbd3a95c
-- title:
--   `BookProof.ChapterPauliFundamental.G_transpose_mul` (μ : Fin 4) (T : Finset (Fin 4)) : (G T)ᵀ * mgamma μ = sgnT μ (stepT μ T) • (G (stepT μ T))ᵀ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliFundamental`.
--
--   `BookProof.ChapterPauliFundamental.G_transpose_mul` (μ : Fin 4) (T : Finset (Fin 4)) : (G T)ᵀ * mgamma μ = sgnT μ (stepT μ T) • (G (stepT μ T))ᵀ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliFundamental.G_transpose_mul`.

-- Generated from ChapterPauliFundamental.lean — theorem BookProof.ChapterPauliFundamental.G_transpose_mul
import Definitions.Def_ChapterGammaCommutant
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Definitions.Def_ChapterA3
open BookProof.ChapterA3
open BookProof.ChapterPauliFundamental


open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

theorem BookProof.ChapterPauliFundamental.G_transpose_mul (μ : Fin 4) (T : Finset (Fin 4)) :
    (G T)ᵀ * mgamma μ = sgnT μ (stepT μ T) • (G (stepT μ T))ᵀ := by sorry
