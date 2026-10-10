-- Prove2me | Theorems.Thm_BookProof_ChapterPauliFundamental_pauli_exists
-- name    : BookProof.ChapterPauliFundamental.pauli_exists
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T09:30:26.791522+00:00
-- url     : https://prove2.me/theorems/5e6b0a8e-eb34-495b-ad10-7e33a166a591
-- title:
--   `BookProof.ChapterPauliFundamental.pauli_exists` {B : Fin 4 → M4} (hA : IsCliffordC A) (hB : IsCliffordC B) : ∃ S : M4, IsUnit S.det ∧ ∀ μ, B μ = S * A μ * S⁻¹
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliFundamental`.
--
--   `BookProof.ChapterPauliFundamental.pauli_exists` {B : Fin 4 → M4} (hA : IsCliffordC A) (hB : IsCliffordC B) : ∃ S : M4, IsUnit S.det ∧ ∀ μ, B μ = S * A μ * S⁻¹
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliFundamental.pauli_exists`.

-- Generated from ChapterPauliFundamental.lean — theorem BookProof.ChapterPauliFundamental.pauli_exists
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

theorem BookProof.ChapterPauliFundamental.pauli_exists {B : Fin 4 → M4} (hA : IsCliffordC A) (hB : IsCliffordC B) :
    ∃ S : M4, IsUnit S.det ∧ ∀ μ, B μ = S * A μ * S⁻¹ := by sorry
