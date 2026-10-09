-- Prove2me | Theorems.Thm_BookProof_ChapterA3_mgamma_clifford
-- name    : BookProof.ChapterA3.mgamma_clifford
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:38:43.703572+00:00
-- url     : https://prove2.me/theorems/b427e19e-b650-4ff9-b7eb-6599fb570f15
-- title:
--   `BookProof.ChapterA3.mgamma_clifford` (μ ν : Fin 4) : mgamma μ * mgamma ν + mgamma ν * mgamma μ = (-2 * minkowski μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3`.
--
--   `BookProof.ChapterA3.mgamma_clifford` (μ ν : Fin 4) : mgamma μ * mgamma ν + mgamma ν * mgamma μ = (-2 * minkowski μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.mgamma_clifford`.

-- Generated from ChapterA3.lean — theorem BookProof.ChapterA3.mgamma_clifford
import Mathlib
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix

theorem BookProof.ChapterA3.mgamma_clifford (μ ν : Fin 4) :
    mgamma μ * mgamma ν + mgamma ν * mgamma μ =
      (-2 * minkowski μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by sorry
