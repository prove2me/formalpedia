-- Prove2me | Theorems.Thm_BookProof_ChapterSphericalBesselODE_gIter_pred_eq
-- name    : BookProof.ChapterSphericalBesselODE.gIter_pred_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:19:12.612922+00:00
-- url     : https://prove2.me/theorems/f932d515-dd0b-4e40-9014-015a59efd05c
-- title:
--   `BookProof.ChapterSphericalBesselODE.gIter_pred_eq` (l : ℕ) {r : ℝ} (hr : r ≠ 0) : gIter l r = (2 * l + 3) * gIter (l + 1) r + r * deriv (gIter (l + 1)) r
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSphericalBesselODE`.
--
--   `BookProof.ChapterSphericalBesselODE.gIter_pred_eq` (l : ℕ) {r : ℝ} (hr : r ≠ 0) : gIter l r = (2 * l + 3) * gIter (l + 1) r + r * deriv (gIter (l + 1)) r
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSphericalBesselODE.gIter_pred_eq`.

-- Generated from ChapterSphericalBesselODE.lean — theorem BookProof.ChapterSphericalBesselODE.gIter_pred_eq
import Definitions.Def_ChapterSphericalBessel
import Mathlib
import Definitions.Def_ChapterSphericalBesselODE
open BookProof.ChapterSphericalBesselODE



open BookProof.ChapterSphericalBessel

theorem BookProof.ChapterSphericalBesselODE.gIter_pred_eq (l : ℕ) {r : ℝ} (hr : r ≠ 0) :
    gIter l r = (2 * l + 3) * gIter (l + 1) r + r * deriv (gIter (l + 1)) r := by sorry
