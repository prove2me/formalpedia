-- Prove2me | Theorems.Thm_BookProof_ChapterA3_paulisigma_trace
-- name    : BookProof.ChapterA3.paulisigma_trace
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T08:25:46.359739+00:00
-- url     : https://prove2.me/theorems/98d4566d-e8a0-477a-827b-458c6d130116
-- title:
--   `BookProof.ChapterA3.paulisigma_trace` (μ ν : Fin 4) : (pauliσ μ * pauliσ ν).trace = if μ = ν then 2 else 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3h`.
--
--   `BookProof.ChapterA3.paulisigma_trace` (μ ν : Fin 4) : (pauliσ μ * pauliσ ν).trace = if μ = ν then 2 else 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.paulisigma_trace`.

-- Generated from ChapterA3h.lean — theorem BookProof.ChapterA3.pauliσ_trace
import Mathlib
import Definitions.Def_ChapterA3h
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.paulisigma_trace (μ ν : Fin 4) :
    (pauliσ μ * pauliσ ν).trace = if μ = ν then 2 else 0 := by sorry
