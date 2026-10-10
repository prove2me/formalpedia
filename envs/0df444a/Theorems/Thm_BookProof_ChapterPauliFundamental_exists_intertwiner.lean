-- Prove2me | Theorems.Thm_BookProof_ChapterPauliFundamental_exists_intertwiner
-- name    : BookProof.ChapterPauliFundamental.exists_intertwiner
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T09:32:42.634477+00:00
-- url     : https://prove2.me/theorems/5a346025-6fac-4059-b9a6-20166ac6b160
-- title:
--   `BookProof.ChapterPauliFundamental.exists_intertwiner` (hA : IsCliffordC A) : ∃ S : M4, IsUnit S.det ∧ ∀ μ, A μ = S * mgamma μ * S⁻¹
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliFundamental`.
--
--   `BookProof.ChapterPauliFundamental.exists_intertwiner` (hA : IsCliffordC A) : ∃ S : M4, IsUnit S.det ∧ ∀ μ, A μ = S * mgamma μ * S⁻¹
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliFundamental.exists_intertwiner`.

-- Generated from ChapterPauliFundamental.lean — theorem BookProof.ChapterPauliFundamental.exists_intertwiner
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

theorem BookProof.ChapterPauliFundamental.exists_intertwiner (hA : IsCliffordC A) :
    ∃ S : M4, IsUnit S.det ∧ ∀ μ, A μ = S * mgamma μ * S⁻¹ := by sorry
