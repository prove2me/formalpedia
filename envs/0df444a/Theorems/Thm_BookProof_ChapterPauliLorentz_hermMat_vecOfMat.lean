-- Prove2me | Theorems.Thm_BookProof_ChapterPauliLorentz_hermMat_vecOfMat
-- name    : BookProof.ChapterPauliLorentz.hermMat_vecOfMat
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T09:31:58.706835+00:00
-- url     : https://prove2.me/theorems/02a5d792-121c-4cad-936c-6a18d3a63b70
-- title:
--   `BookProof.ChapterPauliLorentz.hermMat_vecOfMat` {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : Hᴴ = H) : hermMat (vecOfMat H) = H
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliLorentz`.
--
--   `BookProof.ChapterPauliLorentz.hermMat_vecOfMat` {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : Hᴴ = H) : hermMat (vecOfMat H) = H
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliLorentz.hermMat_vecOfMat`.

-- Generated from ChapterPauliLorentz.lean — theorem BookProof.ChapterPauliLorentz.hermMat_vecOfMat
import Mathlib
import Definitions.Def_ChapterPauliLorentz
open BookProof.ChapterPauliLorentz


open Matrix
open scoped BigOperators

theorem BookProof.ChapterPauliLorentz.hermMat_vecOfMat {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : Hᴴ = H) :
    hermMat (vecOfMat H) = H := by sorry
