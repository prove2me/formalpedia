-- Prove2me | Theorems.Thm_BookProof_ChapterGammaCommutant_gamma_intertwiner_unique
-- name    : BookProof.ChapterGammaCommutant.gamma_intertwiner_unique
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T10:51:55.21054+00:00
-- url     : https://prove2.me/theorems/357f4869-a64d-4ee6-81d1-5c6eada252ba
-- title:
--   `BookProof.ChapterGammaCommutant.gamma_intertwiner_unique` (S T : Matrix (Fin 4) (Fin 4) ℂ) (hS : IsUnit S.det) (hSg : ∀ μ, S * mgamma μ = mgamma μ * S) (hTg : ∀ μ, T * mgamma μ =
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGammaCommutant`.
--
--   `BookProof.ChapterGammaCommutant.gamma_intertwiner_unique` (S T : Matrix (Fin 4) (Fin 4) ℂ) (hS : IsUnit S.det) (hSg : ∀ μ, S * mgamma μ = mgamma μ * S) (hTg : ∀ μ, T * mgamma μ = mgamma μ * T) : ∃ c : ℂ, T = c • S
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGammaCommutant.gamma_intertwiner_unique`.

-- Generated from ChapterGammaCommutant.lean — theorem BookProof.ChapterGammaCommutant.gamma_intertwiner_unique
import Mathlib
import Definitions.Def_ChapterGammaCommutant
import Definitions.Def_ChapterA3
open BookProof.ChapterA3
open BookProof.ChapterGammaCommutant


open Matrix


open BookProof.ChapterA3

theorem BookProof.ChapterGammaCommutant.gamma_intertwiner_unique (S T : Matrix (Fin 4) (Fin 4) ℂ) (hS : IsUnit S.det)
    (hSg : ∀ μ, S * mgamma μ = mgamma μ * S) (hTg : ∀ μ, T * mgamma μ = mgamma μ * T) :
    ∃ c : ℂ, T = c • S := by sorry
