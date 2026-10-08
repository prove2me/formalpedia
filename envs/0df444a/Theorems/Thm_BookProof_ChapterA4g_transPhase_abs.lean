-- Prove2me | Theorems.Thm_BookProof_ChapterA4g_transPhase_abs
-- name    : BookProof.ChapterA4g.transPhase_abs
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:48:00.971528+00:00
-- url     : https://prove2.me/theorems/ec0a8d0d-8bd8-4fb7-9e1a-beb445be0141
-- title:
--   `BookProof.ChapterA4g.transPhase_abs` (p a : Fin 3 → ℝ) : ‖transPhase p a‖ = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA4g`.
--
--   `BookProof.ChapterA4g.transPhase_abs` (p a : Fin 3 → ℝ) : ‖transPhase p a‖ = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA4g.transPhase_abs`.

-- Generated from ChapterA4g.lean — theorem BookProof.ChapterA4g.transPhase_abs
import Definitions.Def_ChapterA3
import Mathlib
import Definitions.Def_ChapterA4g
import Definitions.Def_ChapterLorentzTranslation
open BookProof.ChapterLorentzTranslation
open BookProof.ChapterA4g


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3

theorem BookProof.ChapterA4g.transPhase_abs (p a : Fin 3 → ℝ) :
    ‖transPhase p a‖ = 1 := by sorry
