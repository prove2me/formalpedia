-- Prove2me | Theorems.Thm_BookProof_ChapterA3_det_pauli_comb
-- name    : BookProof.ChapterA3.det_pauli_comb
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:49:22.349402+00:00
-- url     : https://prove2.me/theorems/ef428ec1-621d-41db-a4ee-fa3f6a72d512
-- title:
--   `BookProof.ChapterA3.det_pauli_comb` (x : Fin 4 → ℂ) : (∑ μ, x μ • pauliσ μ).det = Qc x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3h`.
--
--   `BookProof.ChapterA3.det_pauli_comb` (x : Fin 4 → ℂ) : (∑ μ, x μ • pauliσ μ).det = Qc x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.det_pauli_comb`.

-- Generated from ChapterA3h.lean — theorem BookProof.ChapterA3.det_pauli_comb
import Mathlib
import Definitions.Def_ChapterA3h
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.det_pauli_comb (x : Fin 4 → ℂ) :
    (∑ μ, x μ • pauliσ μ).det = Qc x := by sorry
