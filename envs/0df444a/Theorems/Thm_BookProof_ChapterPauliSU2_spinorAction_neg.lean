-- Prove2me | Theorems.Thm_BookProof_ChapterPauliSU2_spinorAction_neg
-- name    : BookProof.ChapterPauliSU2.spinorAction_neg
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T09:33:20.08921+00:00
-- url     : https://prove2.me/theorems/e7fdebb5-93fa-46b0-b65e-84817d28425f
-- title:
--   `BookProof.ChapterPauliSU2.spinorAction_neg` (T X : Matrix (Fin 2) (Fin 2) ℂ) : spinorAction (-T) X = spinorAction T X
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliSU2`.
--
--   `BookProof.ChapterPauliSU2.spinorAction_neg` (T X : Matrix (Fin 2) (Fin 2) ℂ) : spinorAction (-T) X = spinorAction T X
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliSU2.spinorAction_neg`.

-- Generated from ChapterPauliSU2.lean — theorem BookProof.ChapterPauliSU2.spinorAction_neg
import Definitions.Def_ChapterPauliLorentz
import Mathlib
import Definitions.Def_ChapterPauliSU2
open BookProof.ChapterPauliSU2


open Matrix
open scoped BigOperators


open BookProof.ChapterPauliLorentz

theorem BookProof.ChapterPauliSU2.spinorAction_neg (T X : Matrix (Fin 2) (Fin 2) ℂ) :
    spinorAction (-T) X = spinorAction T X := by sorry
