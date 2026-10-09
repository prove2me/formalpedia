-- Prove2me | Theorems.Thm_BookProof_ChapterA3_differentiable_det
-- name    : BookProof.ChapterA3.differentiable_det
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:47:19.109491+00:00
-- url     : https://prove2.me/theorems/f9f95d76-4136-4578-900a-e137ee0cc49f
-- title:
--   `BookProof.ChapterA3.differentiable_det` : Differentiable ℝ (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3f`.
--
--   `BookProof.ChapterA3.differentiable_det` : Differentiable ℝ (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.differentiable_det`.

-- Generated from ChapterA3f.lean — theorem BookProof.ChapterA3.differentiable_det
import Mathlib
import Definitions.Def_ChapterA3f
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix NormedSpace
open scoped Norms.Operator


variable {n : ℕ}

theorem BookProof.ChapterA3.differentiable_det :
    Differentiable ℝ (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ) := by sorry
