-- Prove2me | Theorems.Thm_BookProof_ChapterSphericalBesselODE_hasDerivAt_sbessel_scaled
-- name    : BookProof.ChapterSphericalBesselODE.hasDerivAt_sbessel_scaled
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:21:31.103407+00:00
-- url     : https://prove2.me/theorems/4149c834-19ec-45b6-9dec-cf83d9877227
-- title:
--   `BookProof.ChapterSphericalBesselODE.hasDerivAt_sbessel_scaled` (l : ℕ) {p x : ℝ} (hp : p ≠ 0) (hx : x ≠ 0) : HasDerivAt (fun s : ℝ => sbessel l (p * s)) (deriv (sbessel l) (p * x)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSphericalBesselODE`.
--
--   `BookProof.ChapterSphericalBesselODE.hasDerivAt_sbessel_scaled` (l : ℕ) {p x : ℝ} (hp : p ≠ 0) (hx : x ≠ 0) : HasDerivAt (fun s : ℝ => sbessel l (p * s)) (deriv (sbessel l) (p * x) * p) x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSphericalBesselODE.hasDerivAt_sbessel_scaled`.

-- Generated from ChapterSphericalBesselODE.lean — theorem BookProof.ChapterSphericalBesselODE.hasDerivAt_sbessel_scaled
import Mathlib
import Definitions.Def_ChapterSphericalBesselODE
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBessel
open BookProof.ChapterSphericalBesselODE



open BookProof.ChapterSphericalBessel

theorem BookProof.ChapterSphericalBesselODE.hasDerivAt_sbessel_scaled (l : ℕ) {p x : ℝ} (hp : p ≠ 0) (hx : x ≠ 0) :
    HasDerivAt (fun s : ℝ => sbessel l (p * s)) (deriv (sbessel l) (p * x) * p) x := by sorry
