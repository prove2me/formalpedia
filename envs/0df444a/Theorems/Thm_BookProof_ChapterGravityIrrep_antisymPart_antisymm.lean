-- Prove2me | Theorems.Thm_BookProof_ChapterGravityIrrep_antisymPart_antisymm
-- name    : BookProof.ChapterGravityIrrep.antisymPart_antisymm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T12:58:22.01709+00:00
-- url     : https://prove2.me/theorems/db133065-241a-4b2d-83c4-ddf846aa50b3
-- title:
--   `BookProof.ChapterGravityIrrep.antisymPart_antisymm` (M : Matrix (Fin 3) (Fin 3) ℝ) : (antisymPart M)ᵀ = -(antisymPart M)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityIrrep`.
--
--   `BookProof.ChapterGravityIrrep.antisymPart_antisymm` (M : Matrix (Fin 3) (Fin 3) ℝ) : (antisymPart M)ᵀ = -(antisymPart M)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityIrrep.antisymPart_antisymm`.

-- Generated from ChapterGravityIrrep.lean — theorem BookProof.ChapterGravityIrrep.antisymPart_antisymm
import Mathlib
import Definitions.Def_ChapterGravityIrrep
open BookProof.ChapterGravityIrrep



open Matrix
open scoped BigOperators

theorem BookProof.ChapterGravityIrrep.antisymPart_antisymm (M : Matrix (Fin 3) (Fin 3) ℝ) :
    (antisymPart M)ᵀ = -(antisymPart M) := by sorry
