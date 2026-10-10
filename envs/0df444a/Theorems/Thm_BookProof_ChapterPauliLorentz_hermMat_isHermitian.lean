-- Prove2me | Theorems.Thm_BookProof_ChapterPauliLorentz_hermMat_isHermitian
-- name    : BookProof.ChapterPauliLorentz.hermMat_isHermitian
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T09:33:05.015788+00:00
-- url     : https://prove2.me/theorems/ab604633-7c99-4bc4-84d5-c2ce9944c3fb
-- title:
--   `BookProof.ChapterPauliLorentz.hermMat_isHermitian` (x : Fin 4 → ℝ) : (hermMat x)ᴴ = hermMat x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliLorentz`.
--
--   `BookProof.ChapterPauliLorentz.hermMat_isHermitian` (x : Fin 4 → ℝ) : (hermMat x)ᴴ = hermMat x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliLorentz.hermMat_isHermitian`.

-- Generated from ChapterPauliLorentz.lean — theorem BookProof.ChapterPauliLorentz.hermMat_isHermitian
import Mathlib
import Definitions.Def_ChapterPauliLorentz
open BookProof.ChapterPauliLorentz


open Matrix
open scoped BigOperators

theorem BookProof.ChapterPauliLorentz.hermMat_isHermitian (x : Fin 4 → ℝ) : (hermMat x)ᴴ = hermMat x := by sorry
