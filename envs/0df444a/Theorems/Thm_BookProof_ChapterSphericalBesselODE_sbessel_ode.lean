-- Prove2me | Theorems.Thm_BookProof_ChapterSphericalBesselODE_sbessel_ode
-- name    : BookProof.ChapterSphericalBesselODE.sbessel_ode
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:19:41.598895+00:00
-- url     : https://prove2.me/theorems/0bdd5d6a-85b2-4b5c-b173-d2c3f6d9c030
-- title:
--   `BookProof.ChapterSphericalBesselODE.sbessel_ode` (l : ℕ) {r : ℝ} (hr : r ≠ 0) : r ^ 2 * deriv (deriv (sbessel l)) r + 2 * r * deriv (sbessel l) r + (r ^ 2 - l * (l + 1)) * sbessel
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSphericalBesselODE`.
--
--   `BookProof.ChapterSphericalBesselODE.sbessel_ode` (l : ℕ) {r : ℝ} (hr : r ≠ 0) : r ^ 2 * deriv (deriv (sbessel l)) r + 2 * r * deriv (sbessel l) r + (r ^ 2 - l * (l + 1)) * sbessel l r = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSphericalBesselODE.sbessel_ode`.

-- Generated from ChapterSphericalBesselODE.lean — theorem BookProof.ChapterSphericalBesselODE.sbessel_ode
import Mathlib
import Definitions.Def_ChapterSphericalBesselODE
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBessel
open BookProof.ChapterSphericalBesselODE



open BookProof.ChapterSphericalBessel

theorem BookProof.ChapterSphericalBesselODE.sbessel_ode (l : ℕ) {r : ℝ} (hr : r ≠ 0) :
    r ^ 2 * deriv (deriv (sbessel l)) r + 2 * r * deriv (sbessel l) r
      + (r ^ 2 - l * (l + 1)) * sbessel l r = 0 := by sorry
