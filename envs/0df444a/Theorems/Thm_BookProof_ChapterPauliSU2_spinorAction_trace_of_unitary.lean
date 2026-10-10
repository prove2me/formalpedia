-- Prove2me | Theorems.Thm_BookProof_ChapterPauliSU2_spinorAction_trace_of_unitary
-- name    : BookProof.ChapterPauliSU2.spinorAction_trace_of_unitary
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T09:34:58.857572+00:00
-- url     : https://prove2.me/theorems/b4f0141b-10bf-433a-a41c-a94fe96fb1e7
-- title:
--   `BookProof.ChapterPauliSU2.spinorAction_trace_of_unitary` {T : Matrix (Fin 2) (Fin 2) ℂ} (hT : Tᴴ * T = 1) (X : Matrix (Fin 2) (Fin 2) ℂ) : (spinorAction T X).trace = X.trace
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliSU2`.
--
--   `BookProof.ChapterPauliSU2.spinorAction_trace_of_unitary` {T : Matrix (Fin 2) (Fin 2) ℂ} (hT : Tᴴ * T = 1) (X : Matrix (Fin 2) (Fin 2) ℂ) : (spinorAction T X).trace = X.trace
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliSU2.spinorAction_trace_of_unitary`.

-- Generated from ChapterPauliSU2.lean — theorem BookProof.ChapterPauliSU2.spinorAction_trace_of_unitary
import Definitions.Def_ChapterPauliLorentz
import Mathlib
import Definitions.Def_ChapterPauliSU2
open BookProof.ChapterPauliSU2


open Matrix
open scoped BigOperators


open BookProof.ChapterPauliLorentz

theorem BookProof.ChapterPauliSU2.spinorAction_trace_of_unitary {T : Matrix (Fin 2) (Fin 2) ℂ}
    (hT : Tᴴ * T = 1) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (spinorAction T X).trace = X.trace := by sorry
