-- Prove2me | Theorems.Thm_BookProof_ChapterGravityIrrep_frob_symTraceless_antisym
-- name    : BookProof.ChapterGravityIrrep.frob_symTraceless_antisym
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T12:59:08.908823+00:00
-- url     : https://prove2.me/theorems/e11c5927-4ddf-4769-af09-fc51d2766e48
-- title:
--   `BookProof.ChapterGravityIrrep.frob_symTraceless_antisym` (M : Matrix (Fin 3) (Fin 3) ℝ) : frobInner (symTracelessPart M) (antisymPart M) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGravityIrrep`.
--
--   `BookProof.ChapterGravityIrrep.frob_symTraceless_antisym` (M : Matrix (Fin 3) (Fin 3) ℝ) : frobInner (symTracelessPart M) (antisymPart M) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGravityIrrep.frob_symTraceless_antisym`.

-- Generated from ChapterGravityIrrep.lean — theorem BookProof.ChapterGravityIrrep.frob_symTraceless_antisym
import Mathlib
import Definitions.Def_ChapterGravityIrrep
open BookProof.ChapterGravityIrrep



open Matrix
open scoped BigOperators

theorem BookProof.ChapterGravityIrrep.frob_symTraceless_antisym (M : Matrix (Fin 3) (Fin 3) ℝ) :
    frobInner (symTracelessPart M) (antisymPart M) = 0 := by sorry
