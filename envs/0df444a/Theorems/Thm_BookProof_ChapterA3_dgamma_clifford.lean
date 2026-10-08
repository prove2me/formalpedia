-- Prove2me | Theorems.Thm_BookProof_ChapterA3_dgamma_clifford
-- name    : BookProof.ChapterA3.dgamma_clifford
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:42:05.982984+00:00
-- url     : https://prove2.me/theorems/4842847c-83c0-487a-9a2f-d1bb604d687d
-- title:
--   `BookProof.ChapterA3.dgamma_clifford` (μ ν : Fin 4) : dgamma μ * dgamma ν + dgamma ν * dgamma μ = (2 * minkowski μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3`.
--
--   `BookProof.ChapterA3.dgamma_clifford` (μ ν : Fin 4) : dgamma μ * dgamma ν + dgamma ν * dgamma μ = (2 * minkowski μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.dgamma_clifford`.

-- Generated from ChapterA3.lean — theorem BookProof.ChapterA3.dgamma_clifford
import Mathlib
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix

theorem BookProof.ChapterA3.dgamma_clifford (μ ν : Fin 4) :
    dgamma μ * dgamma ν + dgamma ν * dgamma μ =
      (2 * minkowski μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by sorry
