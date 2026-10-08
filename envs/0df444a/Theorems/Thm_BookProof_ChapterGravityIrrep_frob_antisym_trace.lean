-- Prove2me | Theorems.Thm_BookProof_ChapterGravityIrrep_frob_antisym_trace
-- name    : BookProof.ChapterGravityIrrep.frob_antisym_trace
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T12:59:30.212356+00:00
-- url     : https://prove2.me/theorems/9823c789-b06a-41e2-9670-a2f4be0c7496
-- title:
--   `BookProof.ChapterGravityIrrep.frob_antisym_trace` (M : Matrix (Fin 3) (Fin 3) ℝ) : frobInner (antisymPart M) ((M.trace) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityIrrep`.
--
--   `BookProof.ChapterGravityIrrep.frob_antisym_trace` (M : Matrix (Fin 3) (Fin 3) ℝ) : frobInner (antisymPart M) ((M.trace) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityIrrep.frob_antisym_trace`.

-- Generated from ChapterGravityIrrep.lean — theorem BookProof.ChapterGravityIrrep.frob_antisym_trace
import Mathlib
import Definitions.Def_ChapterGravityIrrep
open BookProof.ChapterGravityIrrep



open Matrix
open scoped BigOperators

theorem BookProof.ChapterGravityIrrep.frob_antisym_trace (M : Matrix (Fin 3) (Fin 3) ℝ) :
    frobInner (antisymPart M) ((M.trace) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) = 0 := by sorry
