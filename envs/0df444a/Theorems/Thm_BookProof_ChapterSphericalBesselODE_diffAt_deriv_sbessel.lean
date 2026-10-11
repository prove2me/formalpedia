-- Prove2me | Theorems.Thm_BookProof_ChapterSphericalBesselODE_diffAt_deriv_sbessel
-- name    : BookProof.ChapterSphericalBesselODE.diffAt_deriv_sbessel
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:21:45.244994+00:00
-- url     : https://prove2.me/theorems/822435f6-3087-45a5-aa56-fb7adf890557
-- title:
--   `BookProof.ChapterSphericalBesselODE.diffAt_deriv_sbessel` (l : ℕ) {x : ℝ} (hx : x ≠ 0) : DifferentiableAt ℝ (deriv (sbessel l)) x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSphericalBesselODE`.
--
--   `BookProof.ChapterSphericalBesselODE.diffAt_deriv_sbessel` (l : ℕ) {x : ℝ} (hx : x ≠ 0) : DifferentiableAt ℝ (deriv (sbessel l)) x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSphericalBesselODE.diffAt_deriv_sbessel`.

-- Generated from ChapterSphericalBesselODE.lean — theorem BookProof.ChapterSphericalBesselODE.diffAt_deriv_sbessel
import Mathlib
import Definitions.Def_ChapterSphericalBesselODE
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBessel
open BookProof.ChapterSphericalBesselODE



open BookProof.ChapterSphericalBessel

theorem BookProof.ChapterSphericalBesselODE.diffAt_deriv_sbessel (l : ℕ) {x : ℝ} (hx : x ≠ 0) :
    DifferentiableAt ℝ (deriv (sbessel l)) x := by sorry
