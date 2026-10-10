-- Prove2me | Theorems.Thm_BookProof_ChapterA3_mgamma_conj_eq_self_iff
-- name    : BookProof.ChapterA3.mgamma_conj_eq_self_iff
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T09:09:44.244883+00:00
-- url     : https://prove2.me/theorems/c5250d04-ecc2-4520-a05b-5b07188f4294
-- title:
--   `BookProof.ChapterA3.mgamma_conj_eq_self_iff` {S : Matrix (Fin 4) (Fin 4) ℂ} (hS : IsUnit S.det) : (∀ μ, S * mgamma μ * S⁻¹ = mgamma μ) ↔ ∃ c : ℂ, c ≠ 0 ∧ S = c • (1 :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliCommutant`.
--
--   `BookProof.ChapterA3.mgamma_conj_eq_self_iff` {S : Matrix (Fin 4) (Fin 4) ℂ} (hS : IsUnit S.det) : (∀ μ, S * mgamma μ * S⁻¹ = mgamma μ) ↔ ∃ c : ℂ, c ≠ 0 ∧ S = c • (1 : Matrix (Fin 4) (Fin 4) ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.mgamma_conj_eq_self_iff`.

-- Generated from ChapterPauliCommutant.lean — theorem BookProof.ChapterA3.mgamma_conj_eq_self_iff
import Mathlib
import Definitions.Def_ChapterPauliCommutant
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix

theorem BookProof.ChapterA3.mgamma_conj_eq_self_iff {S : Matrix (Fin 4) (Fin 4) ℂ} (hS : IsUnit S.det) :
    (∀ μ, S * mgamma μ * S⁻¹ = mgamma μ) ↔
      ∃ c : ℂ, c ≠ 0 ∧ S = c • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by sorry
