-- Prove2me | Theorems.Thm_BookProof_ChapterPauliGrover_pauliX_parametrizes_delta
-- name    : BookProof.ChapterPauliGrover.pauliX_parametrizes_delta
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T09:34:30.706986+00:00
-- url     : https://prove2.me/theorems/b1d2ae64-6f99-4d6b-99e0-4bb2ec78467b
-- title:
--   `BookProof.ChapterPauliGrover.pauliX_parametrizes_delta` (y : Fin 2) : ‖pauliX y 0‖ ^ 2 = (if y = 1 then 1 else 0 : ℝ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliGrover`.
--
--   `BookProof.ChapterPauliGrover.pauliX_parametrizes_delta` (y : Fin 2) : ‖pauliX y 0‖ ^ 2 = (if y = 1 then 1 else 0 : ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliGrover.pauliX_parametrizes_delta`.

-- Generated from ChapterPauliGrover.lean — theorem BookProof.ChapterPauliGrover.pauliX_parametrizes_delta
import Definitions.Def_ChapterConditional
import Mathlib
import Definitions.Def_ChapterPauliGrover
open BookProof.ChapterPauliGrover


open scoped BigOperators Matrix ComplexConjugate
open Matrix
open BookProof.ChapterConditional

theorem BookProof.ChapterPauliGrover.pauliX_parametrizes_delta (y : Fin 2) :
    ‖pauliX y 0‖ ^ 2 = (if y = 1 then 1 else 0 : ℝ) := by sorry
