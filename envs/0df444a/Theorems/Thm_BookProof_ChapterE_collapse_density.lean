-- Prove2me | Theorems.Thm_BookProof_ChapterE_collapse_density
-- name    : BookProof.ChapterE.collapse_density
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T23:09:59.377494+00:00
-- url     : https://prove2.me/theorems/759d2687-c63b-4fac-b031-d826f7e0edd4
-- title:
--   `BookProof.ChapterE.collapse_density` (t : ℝ) : (!![Real.cos t ^ 2, 0; 0, Real.sin t ^ 2] : Matrix (Fin 2) (Fin 2) ℝ) = (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (1 / 2 * Real
-- statement:
--   Prove the following Lean 4 theorem from `ChapterE`.
--
--   `BookProof.ChapterE.collapse_density` (t : ℝ) : (!![Real.cos t ^ 2, 0; 0, Real.sin t ^ 2] : Matrix (Fin 2) (Fin 2) ℝ) = (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (1 / 2 * Real.cos (2 * t)) • !![1, 0; 0, -1]
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterE.collapse_density`.

-- Generated from ChapterE.lean — theorem BookProof.ChapterE.collapse_density
import Mathlib
import Definitions.Def_ChapterE
open BookProof.ChapterE


open scoped Matrix BigOperators
open Filter
open scoped Topology

theorem BookProof.ChapterE.collapse_density (t : ℝ) :
    (!![Real.cos t ^ 2, 0; 0, Real.sin t ^ 2] : Matrix (Fin 2) (Fin 2) ℝ)
      = (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
        + (1 / 2 * Real.cos (2 * t)) • !![1, 0; 0, -1] := by sorry
