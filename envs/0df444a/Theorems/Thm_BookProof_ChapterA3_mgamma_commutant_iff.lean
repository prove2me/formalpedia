-- Prove2me | Theorems.Thm_BookProof_ChapterA3_mgamma_commutant_iff
-- name    : BookProof.ChapterA3.mgamma_commutant_iff
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T09:10:15.650608+00:00
-- url     : https://prove2.me/theorems/a4329d95-5b00-4875-aa5e-35f94d3e8da6
-- title:
--   `BookProof.ChapterA3.mgamma_commutant_iff` (M : Matrix (Fin 4) (Fin 4) ℂ) : (∀ μ, M * mgamma μ = mgamma μ * M) ↔ ∃ c : ℂ, M = c • (1 : Matrix (Fin 4) (Fin 4) ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliCommutant`.
--
--   `BookProof.ChapterA3.mgamma_commutant_iff` (M : Matrix (Fin 4) (Fin 4) ℂ) : (∀ μ, M * mgamma μ = mgamma μ * M) ↔ ∃ c : ℂ, M = c • (1 : Matrix (Fin 4) (Fin 4) ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.mgamma_commutant_iff`.

-- Generated from ChapterPauliCommutant.lean — theorem BookProof.ChapterA3.mgamma_commutant_iff
import Mathlib
import Definitions.Def_ChapterPauliCommutant
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix

theorem BookProof.ChapterA3.mgamma_commutant_iff (M : Matrix (Fin 4) (Fin 4) ℂ) :
    (∀ μ, M * mgamma μ = mgamma μ * M) ↔ ∃ c : ℂ, M = c • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by sorry
