-- Prove2me | Theorems.Thm_BookProof_ChapterPauliLorentz_spinorMap_preserves_mink
-- name    : BookProof.ChapterPauliLorentz.spinorMap_preserves_mink
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T09:32:57.60373+00:00
-- url     : https://prove2.me/theorems/6be61e33-f056-4535-af32-5a3c555d58f3
-- title:
--   `BookProof.ChapterPauliLorentz.spinorMap_preserves_mink` (T : Matrix (Fin 2) (Fin 2) ℂ) (hT : T.det = 1) (x : Fin 4 → ℝ) : mink (vecOfMat (Tᴴ * hermMat x * T)) = mink x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliLorentz`.
--
--   `BookProof.ChapterPauliLorentz.spinorMap_preserves_mink` (T : Matrix (Fin 2) (Fin 2) ℂ) (hT : T.det = 1) (x : Fin 4 → ℝ) : mink (vecOfMat (Tᴴ * hermMat x * T)) = mink x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliLorentz.spinorMap_preserves_mink`.

-- Generated from ChapterPauliLorentz.lean — theorem BookProof.ChapterPauliLorentz.spinorMap_preserves_mink
import Mathlib
import Definitions.Def_ChapterPauliLorentz
open BookProof.ChapterPauliLorentz


open Matrix
open scoped BigOperators

theorem BookProof.ChapterPauliLorentz.spinorMap_preserves_mink (T : Matrix (Fin 2) (Fin 2) ℂ) (hT : T.det = 1)
    (x : Fin 4 → ℝ) :
    mink (vecOfMat (Tᴴ * hermMat x * T)) = mink x := by sorry
