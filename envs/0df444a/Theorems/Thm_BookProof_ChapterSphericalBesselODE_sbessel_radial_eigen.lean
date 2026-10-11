-- Prove2me | Theorems.Thm_BookProof_ChapterSphericalBesselODE_sbessel_radial_eigen
-- name    : BookProof.ChapterSphericalBesselODE.sbessel_radial_eigen
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:20:27.134107+00:00
-- url     : https://prove2.me/theorems/8c1b8241-d497-4435-bc25-bf9c7b98086a
-- title:
--   `BookProof.ChapterSphericalBesselODE.sbessel_radial_eigen` (l : ℕ) {p r : ℝ} (hp : p ≠ 0) (hr : r ≠ 0) : -(deriv (deriv (fun s => sbessel l (p * s))) r + (2 / r) * deriv (fun s =>
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSphericalBesselODE`.
--
--   `BookProof.ChapterSphericalBesselODE.sbessel_radial_eigen` (l : ℕ) {p r : ℝ} (hp : p ≠ 0) (hr : r ≠ 0) : -(deriv (deriv (fun s => sbessel l (p * s))) r + (2 / r) * deriv (fun s => sbessel l (p * s)) r - ((l : ℝ) * (l + 1) / r ^ 2) * sbessel l (p * r)) = p ^ 2 * sbessel l (p * r)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSphericalBesselODE.sbessel_radial_eigen`.

-- Generated from ChapterSphericalBesselODE.lean — theorem BookProof.ChapterSphericalBesselODE.sbessel_radial_eigen
import Mathlib
import Definitions.Def_ChapterSphericalBesselODE
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBessel
open BookProof.ChapterSphericalBesselODE



open BookProof.ChapterSphericalBessel

theorem BookProof.ChapterSphericalBesselODE.sbessel_radial_eigen (l : ℕ) {p r : ℝ} (hp : p ≠ 0) (hr : r ≠ 0) :
    -(deriv (deriv (fun s => sbessel l (p * s))) r
        + (2 / r) * deriv (fun s => sbessel l (p * s)) r
        - ((l : ℝ) * (l + 1) / r ^ 2) * sbessel l (p * r))
      = p ^ 2 * sbessel l (p * r) := by sorry
