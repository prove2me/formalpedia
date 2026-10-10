-- Prove2me | Theorems.Thm_BookProof_ChapterA3_mgamma_conjugation_unique_up_to_scalar
-- name    : BookProof.ChapterA3.mgamma_conjugation_unique_up_to_scalar
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T09:09:59.318209+00:00
-- url     : https://prove2.me/theorems/837ad01c-e21c-4d24-999e-63e9079708e9
-- title:
--   `BookProof.ChapterA3.mgamma_conjugation_unique_up_to_scalar` {S T : Matrix (Fin 4) (Fin 4) ℂ} (hS : IsUnit S.det) (hT : IsUnit T.det) (h : ∀ μ, S * mgamma μ * S⁻¹ = T * mgamma μ *
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliCommutant`.
--
--   `BookProof.ChapterA3.mgamma_conjugation_unique_up_to_scalar` {S T : Matrix (Fin 4) (Fin 4) ℂ} (hS : IsUnit S.det) (hT : IsUnit T.det) (h : ∀ μ, S * mgamma μ * S⁻¹ = T * mgamma μ * T⁻¹) : ∃ c : ℂ, c ≠ 0 ∧ S = c • T
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.mgamma_conjugation_unique_up_to_scalar`.

-- Generated from ChapterPauliCommutant.lean — theorem BookProof.ChapterA3.mgamma_conjugation_unique_up_to_scalar
import Mathlib
import Definitions.Def_ChapterPauliCommutant
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix

theorem BookProof.ChapterA3.mgamma_conjugation_unique_up_to_scalar
    {S T : Matrix (Fin 4) (Fin 4) ℂ} (hS : IsUnit S.det) (hT : IsUnit T.det)
    (h : ∀ μ, S * mgamma μ * S⁻¹ = T * mgamma μ * T⁻¹) :
    ∃ c : ℂ, c ≠ 0 ∧ S = c • T := by sorry
