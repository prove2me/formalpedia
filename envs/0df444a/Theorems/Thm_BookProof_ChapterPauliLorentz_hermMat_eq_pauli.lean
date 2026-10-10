-- Prove2me | Theorems.Thm_BookProof_ChapterPauliLorentz_hermMat_eq_pauli
-- name    : BookProof.ChapterPauliLorentz.hermMat_eq_pauli
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:31:47.796644+00:00
-- url     : https://prove2.me/theorems/ddb90835-f5cf-4930-9e4e-2138b882d516
-- title:
--   `BookProof.ChapterPauliLorentz.hermMat_eq_pauli` (x : Fin 4 → ℝ) : hermMat x = (x 0 : ℂ) • σ0 + (x 1 : ℂ) • σ1 + (x 2 : ℂ) • σ2 + (x 3 : ℂ) • σ3
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPauliLorentz`.
--
--   `BookProof.ChapterPauliLorentz.hermMat_eq_pauli` (x : Fin 4 → ℝ) : hermMat x = (x 0 : ℂ) • σ0 + (x 1 : ℂ) • σ1 + (x 2 : ℂ) • σ2 + (x 3 : ℂ) • σ3
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPauliLorentz.hermMat_eq_pauli`.

-- Generated from ChapterPauliLorentz.lean — theorem BookProof.ChapterPauliLorentz.hermMat_eq_pauli
import Mathlib
import Definitions.Def_ChapterPauliLorentz
open BookProof.ChapterPauliLorentz


open Matrix
open scoped BigOperators

theorem BookProof.ChapterPauliLorentz.hermMat_eq_pauli (x : Fin 4 → ℝ) :
    hermMat x = (x 0 : ℂ) • σ0 + (x 1 : ℂ) • σ1 + (x 2 : ℂ) • σ2 + (x 3 : ℂ) • σ3 := by sorry
