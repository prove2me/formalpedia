-- Prove2me | Theorems.Thm_BookProof_NsCutoffUniformity_totalDegree_redFormPoly_le
-- name    : BookProof.NsCutoffUniformity.totalDegree_redFormPoly_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T22:17:24.407373+00:00
-- url     : https://prove2.me/theorems/e56e53f3-7e6b-4b82-8503-305592e961fd
-- title:
--   `BookProof.NsCutoffUniformity.totalDegree_redFormPoly_le` (p : Fin n) (r : Fin 7) : (redFormPoly nu k n p r).totalDegree ≤ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsCutoffUniformity`.
--
--   `BookProof.NsCutoffUniformity.totalDegree_redFormPoly_le` (p : Fin n) (r : Fin 7) : (redFormPoly nu k n p r).totalDegree ≤ 2
--
--   Formalization note: Lean 4 identifier `BookProof.NsCutoffUniformity.totalDegree_redFormPoly_le`.

-- Generated from ChapterNsCutoffUniformity.lean — theorem BookProof.NsCutoffUniformity.totalDegree_redFormPoly_le
import Definitions.Def_ChapterNavierStokesFullEulerianFock
import Mathlib
import Definitions.Def_ChapterNsCutoffUniformity



open MvPolynomial BookProof.NsFullEuler

noncomputable section

variable {n : ℕ}

variable {ι : Type*}
variable (nu : ℝ) (k : Fin 3 → ℝ)

theorem BookProof.NsCutoffUniformity.totalDegree_redFormPoly_le (p : Fin n) (r : Fin 7) :
    (redFormPoly nu k n p r).totalDegree ≤ 2 := by sorry
