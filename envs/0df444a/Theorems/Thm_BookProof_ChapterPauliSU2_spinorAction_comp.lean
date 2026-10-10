-- Prove2me | Theorems.Thm_BookProof_ChapterPauliSU2_spinorAction_comp
-- name    : BookProof.ChapterPauliSU2.spinorAction_comp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T09:32:42.763385+00:00
-- url     : https://prove2.me/theorems/74475453-464a-425b-9be6-76f730cb612b
-- title:
--   `BookProof.ChapterPauliSU2.spinorAction_comp` (T₁ T₂ X : Matrix (Fin 2) (Fin 2) ℂ) : spinorAction (T₁ * T₂) X = spinorAction T₂ (spinorAction T₁ X)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliSU2`.
--
--   `BookProof.ChapterPauliSU2.spinorAction_comp` (T₁ T₂ X : Matrix (Fin 2) (Fin 2) ℂ) : spinorAction (T₁ * T₂) X = spinorAction T₂ (spinorAction T₁ X)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliSU2.spinorAction_comp`.

-- Generated from ChapterPauliSU2.lean — theorem BookProof.ChapterPauliSU2.spinorAction_comp
import Definitions.Def_ChapterPauliLorentz
import Mathlib
import Definitions.Def_ChapterPauliSU2
open BookProof.ChapterPauliSU2


open Matrix
open scoped BigOperators


open BookProof.ChapterPauliLorentz

theorem BookProof.ChapterPauliSU2.spinorAction_comp (T₁ T₂ X : Matrix (Fin 2) (Fin 2) ℂ) :
    spinorAction (T₁ * T₂) X = spinorAction T₂ (spinorAction T₁ X) := by sorry
