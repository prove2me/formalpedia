-- Prove2me | Theorems.Thm_BookProof_ChapterSphericalBesselODE_hasDerivAt_sbessel
-- name    : BookProof.ChapterSphericalBesselODE.hasDerivAt_sbessel
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:20:19.604202+00:00
-- url     : https://prove2.me/theorems/8092455e-e7e9-4686-8833-5d5757d5d730
-- title:
--   `BookProof.ChapterSphericalBesselODE.hasDerivAt_sbessel` (l : ℕ) {r : ℝ} (hr : r ≠ 0) : HasDerivAt (sbessel l) (r ^ l * ((l : ℝ) * gIter l r / r + deriv (gIter l) r)) r
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSphericalBesselODE`.
--
--   `BookProof.ChapterSphericalBesselODE.hasDerivAt_sbessel` (l : ℕ) {r : ℝ} (hr : r ≠ 0) : HasDerivAt (sbessel l) (r ^ l * ((l : ℝ) * gIter l r / r + deriv (gIter l) r)) r
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSphericalBesselODE.hasDerivAt_sbessel`.

-- Generated from ChapterSphericalBesselODE.lean — theorem BookProof.ChapterSphericalBesselODE.hasDerivAt_sbessel
import Mathlib
import Definitions.Def_ChapterSphericalBesselODE
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBessel
open BookProof.ChapterSphericalBesselODE



open BookProof.ChapterSphericalBessel

theorem BookProof.ChapterSphericalBesselODE.hasDerivAt_sbessel (l : ℕ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (sbessel l) (r ^ l * ((l : ℝ) * gIter l r / r + deriv (gIter l) r)) r := by sorry
