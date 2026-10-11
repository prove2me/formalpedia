-- Prove2me | Theorems.Thm_BookProof_ChapterSphericalBesselODE_sbessel_rayleigh_raise
-- name    : BookProof.ChapterSphericalBesselODE.sbessel_rayleigh_raise
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:20:23.677982+00:00
-- url     : https://prove2.me/theorems/4c7e9bdf-0dfe-4d54-9413-da45fda50888
-- title:
--   `BookProof.ChapterSphericalBesselODE.sbessel_rayleigh_raise` (l : ℕ) {r : ℝ} (hr : r ≠ 0) : sbessel (l + 1) r = -(r ^ l) * deriv (fun s => sbessel l s / s ^ l) r
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSphericalBesselODE`.
--
--   `BookProof.ChapterSphericalBesselODE.sbessel_rayleigh_raise` (l : ℕ) {r : ℝ} (hr : r ≠ 0) : sbessel (l + 1) r = -(r ^ l) * deriv (fun s => sbessel l s / s ^ l) r
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSphericalBesselODE.sbessel_rayleigh_raise`.

-- Generated from ChapterSphericalBesselODE.lean — theorem BookProof.ChapterSphericalBesselODE.sbessel_rayleigh_raise
import Mathlib
import Definitions.Def_ChapterSphericalBesselODE
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBessel
open BookProof.ChapterSphericalBesselODE



open BookProof.ChapterSphericalBessel

theorem BookProof.ChapterSphericalBesselODE.sbessel_rayleigh_raise (l : ℕ) {r : ℝ} (hr : r ≠ 0) :
    sbessel (l + 1) r = -(r ^ l) * deriv (fun s => sbessel l s / s ^ l) r := by sorry
