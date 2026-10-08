-- Prove2me | Theorems.Thm_BookProof_ChapterEulerStochastic_uniform_to_vertex_singular
-- name    : BookProof.ChapterEulerStochastic.uniform_to_vertex_singular
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:44:22.343791+00:00
-- url     : https://prove2.me/theorems/911f1c81-2e31-4edc-a0c1-c97a2ba4b3c3
-- title:
--   `BookProof.ChapterEulerStochastic.uniform_to_vertex_singular` (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : PreservesProb M) (hcollapse : M *ᵥ ![1 / 2, 1 / 2] = ![1, 0]) : M.det = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerStochastic`.
--
--   `BookProof.ChapterEulerStochastic.uniform_to_vertex_singular` (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : PreservesProb M) (hcollapse : M *ᵥ ![1 / 2, 1 / 2] = ![1, 0]) : M.det = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerStochastic.uniform_to_vertex_singular`.

-- Generated from ChapterEulerStochastic.lean — theorem BookProof.ChapterEulerStochastic.uniform_to_vertex_singular
import Mathlib
import Definitions.Def_ChapterEulerStochastic
open BookProof.ChapterEulerStochastic


open scoped Matrix BigOperators

theorem BookProof.ChapterEulerStochastic.uniform_to_vertex_singular (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : PreservesProb M) (hcollapse : M *ᵥ ![1 / 2, 1 / 2] = ![1, 0]) :
    M.det = 0 := by sorry
