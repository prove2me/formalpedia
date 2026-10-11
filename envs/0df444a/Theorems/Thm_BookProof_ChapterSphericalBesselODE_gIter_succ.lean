-- Prove2me | Theorems.Thm_BookProof_ChapterSphericalBesselODE_gIter_succ
-- name    : BookProof.ChapterSphericalBesselODE.gIter_succ
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:58:54.089346+00:00
-- url     : https://prove2.me/theorems/d8bd185d-02ed-4113-8a47-ef51e63d58e7
-- title:
--   `BookProof.ChapterSphericalBesselODE.gIter_succ` (l : ℕ) (r : ℝ) : gIter (l + 1) r = -(1 / r) * deriv (gIter l) r
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSphericalBesselODE`.
--
--   `BookProof.ChapterSphericalBesselODE.gIter_succ` (l : ℕ) (r : ℝ) : gIter (l + 1) r = -(1 / r) * deriv (gIter l) r
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSphericalBesselODE.gIter_succ`.

-- Generated from ChapterSphericalBesselODE.lean — theorem BookProof.ChapterSphericalBesselODE.gIter_succ
import Mathlib
import Definitions.Def_ChapterSphericalBesselODE
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBessel
open BookProof.ChapterSphericalBesselODE



open BookProof.ChapterSphericalBessel

theorem BookProof.ChapterSphericalBesselODE.gIter_succ (l : ℕ) (r : ℝ) : gIter (l + 1) r = -(1 / r) * deriv (gIter l) r := by sorry
