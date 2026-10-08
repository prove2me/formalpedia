-- Prove2me | Theorems.Thm_BookProof_ChapterA3_pauliCoeff_comb
-- name    : BookProof.ChapterA3.pauliCoeff_comb
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:48:31.203132+00:00
-- url     : https://prove2.me/theorems/087af638-6654-4fd2-9de5-f13b96e66cc1
-- title:
--   `BookProof.ChapterA3.pauliCoeff_comb` (c : Fin 4 → ℂ) (μ : Fin 4) : pauliCoeff (∑ ν, c ν • pauliσ ν) μ = c μ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3h`.
--
--   `BookProof.ChapterA3.pauliCoeff_comb` (c : Fin 4 → ℂ) (μ : Fin 4) : pauliCoeff (∑ ν, c ν • pauliσ ν) μ = c μ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.pauliCoeff_comb`.

-- Generated from ChapterA3h.lean — theorem BookProof.ChapterA3.pauliCoeff_comb
import Mathlib
import Definitions.Def_ChapterA3h
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.pauliCoeff_comb (c : Fin 4 → ℂ) (μ : Fin 4) :
    pauliCoeff (∑ ν, c ν • pauliσ ν) μ = c μ := by sorry
