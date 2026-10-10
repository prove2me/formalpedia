-- Prove2me | Theorems.Thm_BookProof_ChapterPauliFundamental_pauli_unique
-- name    : BookProof.ChapterPauliFundamental.pauli_unique
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T09:30:35.556983+00:00
-- url     : https://prove2.me/theorems/94c859e6-8dd0-463c-8fb2-554e083bc39e
-- title:
--   `BookProof.ChapterPauliFundamental.pauli_unique` {B : Fin 4 → M4} (hA : IsCliffordC A) (S T : M4) (hS : IsUnit S.det) (hT : IsUnit T.det) (hSeq : ∀ μ, B μ = S * A μ * S⁻¹) (hTeq :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliFundamental`.
--
--   `BookProof.ChapterPauliFundamental.pauli_unique` {B : Fin 4 → M4} (hA : IsCliffordC A) (S T : M4) (hS : IsUnit S.det) (hT : IsUnit T.det) (hSeq : ∀ μ, B μ = S * A μ * S⁻¹) (hTeq : ∀ μ, B μ = T * A μ * T⁻¹) : ∃ c : ℂ, c ≠ 0 ∧ T = c • S
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliFundamental.pauli_unique`.

-- Generated from ChapterPauliFundamental.lean — theorem BookProof.ChapterPauliFundamental.pauli_unique
import Definitions.Def_ChapterGammaCommutant
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3b
open BookProof.ChapterA3
open BookProof.ChapterPauliFundamental


open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

theorem BookProof.ChapterPauliFundamental.pauli_unique {B : Fin 4 → M4} (hA : IsCliffordC A)
    (S T : M4) (hS : IsUnit S.det) (hT : IsUnit T.det)
    (hSeq : ∀ μ, B μ = S * A μ * S⁻¹) (hTeq : ∀ μ, B μ = T * A μ * T⁻¹) :
    ∃ c : ℂ, c ≠ 0 ∧ T = c • S := by sorry
