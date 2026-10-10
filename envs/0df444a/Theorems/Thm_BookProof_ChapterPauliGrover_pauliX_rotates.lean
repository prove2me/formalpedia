-- Prove2me | Theorems.Thm_BookProof_ChapterPauliGrover_pauliX_rotates
-- name    : BookProof.ChapterPauliGrover.pauliX_rotates
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:31:33.683706+00:00
-- url     : https://prove2.me/theorems/8056b010-5d3c-4a45-a728-30e8a8257302
-- title:
--   `BookProof.ChapterPauliGrover.pauliX_rotates` : pauliX 1 0 = 1 ∧ pauliX 0 0 = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliGrover`.
--
--   `BookProof.ChapterPauliGrover.pauliX_rotates` : pauliX 1 0 = 1 ∧ pauliX 0 0 = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliGrover.pauliX_rotates`.

-- Generated from ChapterPauliGrover.lean — theorem BookProof.ChapterPauliGrover.pauliX_rotates
import Definitions.Def_ChapterConditional
import Mathlib
import Definitions.Def_ChapterPauliGrover
open BookProof.ChapterPauliGrover


open scoped BigOperators Matrix ComplexConjugate
open Matrix
open BookProof.ChapterConditional

theorem BookProof.ChapterPauliGrover.pauliX_rotates : pauliX 1 0 = 1 ∧ pauliX 0 0 = 0 := by sorry
