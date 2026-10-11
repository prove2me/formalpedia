-- Prove2me | Theorems.Thm_BookProof_ChapterSphericalBesselODE_sbessel_eq
-- name    : BookProof.ChapterSphericalBesselODE.sbessel_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:58:27.130313+00:00
-- url     : https://prove2.me/theorems/86c41fa5-2c23-4000-99ae-9ae5a9c3ccc8
-- title:
--   `BookProof.ChapterSphericalBesselODE.sbessel_eq` (l : ℕ) (r : ℝ) : sbessel l r = r ^ l * gIter l r
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSphericalBesselODE`.
--
--   `BookProof.ChapterSphericalBesselODE.sbessel_eq` (l : ℕ) (r : ℝ) : sbessel l r = r ^ l * gIter l r
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSphericalBesselODE.sbessel_eq`.

-- Generated from ChapterSphericalBesselODE.lean — theorem BookProof.ChapterSphericalBesselODE.sbessel_eq
import Mathlib
import Definitions.Def_ChapterSphericalBesselODE
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBessel
open BookProof.ChapterSphericalBesselODE



open BookProof.ChapterSphericalBessel

theorem BookProof.ChapterSphericalBesselODE.sbessel_eq (l : ℕ) (r : ℝ) : sbessel l r = r ^ l * gIter l r := by sorry
