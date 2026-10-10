-- Prove2me | Theorems.Thm_BookProof_ChapterPauliLorentz_det_hermMat
-- name    : BookProof.ChapterPauliLorentz.det_hermMat
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:31:48.989978+00:00
-- url     : https://prove2.me/theorems/bc979bfa-a940-4d68-91ac-dfd061a76e6d
-- title:
--   `BookProof.ChapterPauliLorentz.det_hermMat` (x : Fin 4 → ℝ) : (hermMat x).det = (mink x : ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliLorentz`.
--
--   `BookProof.ChapterPauliLorentz.det_hermMat` (x : Fin 4 → ℝ) : (hermMat x).det = (mink x : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliLorentz.det_hermMat`.

-- Generated from ChapterPauliLorentz.lean — theorem BookProof.ChapterPauliLorentz.det_hermMat
import Mathlib
import Definitions.Def_ChapterPauliLorentz
open BookProof.ChapterPauliLorentz


open Matrix
open scoped BigOperators

theorem BookProof.ChapterPauliLorentz.det_hermMat (x : Fin 4 → ℝ) : (hermMat x).det = (mink x : ℂ) := by sorry
