-- Prove2me | Theorems.Thm_BookProof_ChapterA3_mgammaZ_clifford
-- name    : BookProof.ChapterA3.mgammaZ_clifford
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:37:28.252666+00:00
-- url     : https://prove2.me/theorems/d43c47d3-c59c-4639-aa08-02630f0cc696
-- title:
--   `BookProof.ChapterA3.mgammaZ_clifford` (μ ν : Fin 4) : mgammaZ μ * mgammaZ ν + mgammaZ ν * mgammaZ μ = (-2 * minkowskiZ μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℤ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3`.
--
--   `BookProof.ChapterA3.mgammaZ_clifford` (μ ν : Fin 4) : mgammaZ μ * mgammaZ ν + mgammaZ ν * mgammaZ μ = (-2 * minkowskiZ μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℤ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.mgammaZ_clifford`.

-- Generated from ChapterA3.lean — theorem BookProof.ChapterA3.mgammaZ_clifford
import Mathlib
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix

theorem BookProof.ChapterA3.mgammaZ_clifford (μ ν : Fin 4) :
    mgammaZ μ * mgammaZ ν + mgammaZ ν * mgammaZ μ =
      (-2 * minkowskiZ μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by sorry
