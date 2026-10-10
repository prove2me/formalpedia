-- Prove2me | Theorems.Thm_BookProof_ChapterPauliFundamental_intertwiner_isUnit
-- name    : BookProof.ChapterPauliFundamental.intertwiner_isUnit
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:30:00.864983+00:00
-- url     : https://prove2.me/theorems/c0afa86a-384f-4efe-ae9c-c0de4db11f66
-- title:
--   `BookProof.ChapterPauliFundamental.intertwiner_isUnit` {S : M4} (hS0 : S ≠ 0) (hSint : ∀ μ, A μ * S = S * mgamma μ) : IsUnit S.det
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliFundamental`.
--
--   `BookProof.ChapterPauliFundamental.intertwiner_isUnit` {S : M4} (hS0 : S ≠ 0) (hSint : ∀ μ, A μ * S = S * mgamma μ) : IsUnit S.det
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliFundamental.intertwiner_isUnit`.

-- Generated from ChapterPauliFundamental.lean — theorem BookProof.ChapterPauliFundamental.intertwiner_isUnit
import Definitions.Def_ChapterGammaCommutant
import Mathlib
import Definitions.Def_ChapterPauliFundamental
import Definitions.Def_ChapterA3
open BookProof.ChapterA3
open BookProof.ChapterPauliFundamental


open Matrix Finset


open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

variable {A : Fin 4 → M4}

theorem BookProof.ChapterPauliFundamental.intertwiner_isUnit {S : M4} (hS0 : S ≠ 0) (hSint : ∀ μ, A μ * S = S * mgamma μ) :
    IsUnit S.det := by sorry
