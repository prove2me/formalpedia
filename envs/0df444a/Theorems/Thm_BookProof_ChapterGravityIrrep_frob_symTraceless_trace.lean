-- Prove2me | Theorems.Thm_BookProof_ChapterGravityIrrep_frob_symTraceless_trace
-- name    : BookProof.ChapterGravityIrrep.frob_symTraceless_trace
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T12:59:31.20569+00:00
-- url     : https://prove2.me/theorems/e30995ae-469f-4c75-a86e-7b5411f7d5b5
-- title:
--   `BookProof.ChapterGravityIrrep.frob_symTraceless_trace` (M : Matrix (Fin 3) (Fin 3) ℝ) : frobInner (symTracelessPart M) ((M.trace) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityIrrep`.
--
--   `BookProof.ChapterGravityIrrep.frob_symTraceless_trace` (M : Matrix (Fin 3) (Fin 3) ℝ) : frobInner (symTracelessPart M) ((M.trace) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityIrrep.frob_symTraceless_trace`.

-- Generated from ChapterGravityIrrep.lean — theorem BookProof.ChapterGravityIrrep.frob_symTraceless_trace
import Mathlib
import Definitions.Def_ChapterGravityIrrep
open BookProof.ChapterGravityIrrep



open Matrix
open scoped BigOperators

theorem BookProof.ChapterGravityIrrep.frob_symTraceless_trace (M : Matrix (Fin 3) (Fin 3) ℝ) :
    frobInner (symTracelessPart M) ((M.trace) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) = 0 := by sorry
