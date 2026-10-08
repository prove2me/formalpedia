-- Prove2me | Theorems.Thm_BookProof_ChapterA3_SEtwo_lower_triangular
-- name    : BookProof.ChapterA3.SEtwo_lower_triangular
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:11:25.618357+00:00
-- url     : https://prove2.me/theorems/9ef1011c-86fc-4874-9767-088018c7f31c
-- title:
--   `BookProof.ChapterA3.SEtwo_lower_triangular` (T : Matrix (Fin 2) (Fin 2) ℂ) (hT : T ∈ SEtwo) : T 0 1 = 0 ∧ T 1 1 = (T 0 0)⁻¹ ∧ Complex.normSq (T 0 0) = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA4d`.
--
--   `BookProof.ChapterA3.SEtwo_lower_triangular` (T : Matrix (Fin 2) (Fin 2) ℂ) (hT : T ∈ SEtwo) : T 0 1 = 0 ∧ T 1 1 = (T 0 0)⁻¹ ∧ Complex.normSq (T 0 0) = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.SEtwo_lower_triangular`.

-- Generated from ChapterA4d.lean — theorem BookProof.ChapterA3.SEtwo_lower_triangular
import Mathlib
import Definitions.Def_ChapterA4d
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.SEtwo_lower_triangular (T : Matrix (Fin 2) (Fin 2) ℂ) (hT : T ∈ SEtwo) :
    T 0 1 = 0 ∧ T 1 1 = (T 0 0)⁻¹ ∧ Complex.normSq (T 0 0) = 1 := by sorry
