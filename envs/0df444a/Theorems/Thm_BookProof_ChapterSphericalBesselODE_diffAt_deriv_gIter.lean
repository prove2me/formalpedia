-- Prove2me | Theorems.Thm_BookProof_ChapterSphericalBesselODE_diffAt_deriv_gIter
-- name    : BookProof.ChapterSphericalBesselODE.diffAt_deriv_gIter
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:58:47.709587+00:00
-- url     : https://prove2.me/theorems/5dce9066-63f1-42e8-98d6-c19454e92819
-- title:
--   `BookProof.ChapterSphericalBesselODE.diffAt_deriv_gIter` (l : ℕ) {r : ℝ} (hr : r ≠ 0) : DifferentiableAt ℝ (deriv (gIter l)) r
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSphericalBesselODE`.
--
--   `BookProof.ChapterSphericalBesselODE.diffAt_deriv_gIter` (l : ℕ) {r : ℝ} (hr : r ≠ 0) : DifferentiableAt ℝ (deriv (gIter l)) r
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSphericalBesselODE.diffAt_deriv_gIter`.

-- Generated from ChapterSphericalBesselODE.lean — theorem BookProof.ChapterSphericalBesselODE.diffAt_deriv_gIter
import Definitions.Def_ChapterSphericalBessel
import Mathlib
import Definitions.Def_ChapterSphericalBesselODE
open BookProof.ChapterSphericalBesselODE



open BookProof.ChapterSphericalBessel

theorem BookProof.ChapterSphericalBesselODE.diffAt_deriv_gIter (l : ℕ) {r : ℝ} (hr : r ≠ 0) :
    DifferentiableAt ℝ (deriv (gIter l)) r := by sorry
