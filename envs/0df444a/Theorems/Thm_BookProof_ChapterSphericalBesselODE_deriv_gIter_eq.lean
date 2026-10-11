-- Prove2me | Theorems.Thm_BookProof_ChapterSphericalBesselODE_deriv_gIter_eq
-- name    : BookProof.ChapterSphericalBesselODE.deriv_gIter_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:19:44.81552+00:00
-- url     : https://prove2.me/theorems/b4145267-0691-4aef-8a8b-44e298ca8c75
-- title:
--   `BookProof.ChapterSphericalBesselODE.deriv_gIter_eq` (l : ℕ) {r : ℝ} (hr : r ≠ 0) : deriv (gIter l) r = -r * gIter (l + 1) r
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSphericalBesselODE`.
--
--   `BookProof.ChapterSphericalBesselODE.deriv_gIter_eq` (l : ℕ) {r : ℝ} (hr : r ≠ 0) : deriv (gIter l) r = -r * gIter (l + 1) r
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSphericalBesselODE.deriv_gIter_eq`.

-- Generated from ChapterSphericalBesselODE.lean — theorem BookProof.ChapterSphericalBesselODE.deriv_gIter_eq
import Definitions.Def_ChapterSphericalBessel
import Mathlib
import Definitions.Def_ChapterSphericalBesselODE
open BookProof.ChapterSphericalBesselODE



open BookProof.ChapterSphericalBessel

theorem BookProof.ChapterSphericalBesselODE.deriv_gIter_eq (l : ℕ) {r : ℝ} (hr : r ≠ 0) :
    deriv (gIter l) r = -r * gIter (l + 1) r := by sorry
