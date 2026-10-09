-- Prove2me | Theorems.Thm_BookProof_ChapterGravityIrrep_irrep_reconstruction
-- name    : BookProof.ChapterGravityIrrep.irrep_reconstruction
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:45:14.441182+00:00
-- url     : https://prove2.me/theorems/ef7d1c9c-25b8-429a-a4e7-f67d4392f45b
-- title:
--   `BookProof.ChapterGravityIrrep.irrep_reconstruction` (M : Matrix (Fin 3) (Fin 3) ℝ) : (1 / 2 : ℝ) • symTracelessPart M + (1 / 2 : ℝ) • antisymPart M + (1 / 3 : ℝ) • (M.trace) • (1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityIrrep`.
--
--   `BookProof.ChapterGravityIrrep.irrep_reconstruction` (M : Matrix (Fin 3) (Fin 3) ℝ) : (1 / 2 : ℝ) • symTracelessPart M + (1 / 2 : ℝ) • antisymPart M + (1 / 3 : ℝ) • (M.trace) • (1 : Matrix (Fin 3) (Fin 3) ℝ) = M
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityIrrep.irrep_reconstruction`.

-- Generated from ChapterGravityIrrep.lean — theorem BookProof.ChapterGravityIrrep.irrep_reconstruction
import Mathlib
import Definitions.Def_ChapterGravityIrrep
open BookProof.ChapterGravityIrrep



open Matrix
open scoped BigOperators

theorem BookProof.ChapterGravityIrrep.irrep_reconstruction (M : Matrix (Fin 3) (Fin 3) ℝ) :
    (1 / 2 : ℝ) • symTracelessPart M + (1 / 2 : ℝ) • antisymPart M
      + (1 / 3 : ℝ) • (M.trace) • (1 : Matrix (Fin 3) (Fin 3) ℝ) = M := by sorry
