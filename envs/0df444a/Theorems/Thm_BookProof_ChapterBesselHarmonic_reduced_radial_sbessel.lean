-- Prove2me | Theorems.Thm_BookProof_ChapterBesselHarmonic_reduced_radial_sbessel
-- name    : BookProof.ChapterBesselHarmonic.reduced_radial_sbessel
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:54:50.442412+00:00
-- url     : https://prove2.me/theorems/d00eceb5-639c-4434-93d1-09001611815c
-- title:
--   `BookProof.ChapterBesselHarmonic.reduced_radial_sbessel` (l : ℕ) {p r : ℝ} (hp : p ≠ 0) (hr : r ≠ 0) : deriv (deriv fun s => sbessel l (p * s) / s ^ l) r + ((2 + 2 * (l : ℝ)) / r)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBesselHarmonic`.
--
--   `BookProof.ChapterBesselHarmonic.reduced_radial_sbessel` (l : ℕ) {p r : ℝ} (hp : p ≠ 0) (hr : r ≠ 0) : deriv (deriv fun s => sbessel l (p * s) / s ^ l) r + ((2 + 2 * (l : ℝ)) / r) * deriv (fun s => sbessel l (p * s) / s ^ l) r = -(p ^ 2) * (sbessel l (p * r) / r ^ l)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBesselHarmonic.reduced_radial_sbessel`.

-- Generated from ChapterBesselHarmonic.lean — theorem BookProof.ChapterBesselHarmonic.reduced_radial_sbessel
import Definitions.Def_ChapterSphericalBesselODE
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
import Mathlib
import Definitions.Def_ChapterBesselHarmonic
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBessel
open BookProof.ChapterBesselHarmonic



open Filter Laplacian InnerProductSpace
open BookProof.ChapterSphericalBessel BookProof.ChapterSphericalBesselODE
open BookProof.ChapterRadialLaplacian BookProof.ChapterLaplacianProduct
open scoped InnerProductSpace RealInnerProductSpace

theorem BookProof.ChapterBesselHarmonic.reduced_radial_sbessel (l : ℕ) {p r : ℝ} (hp : p ≠ 0) (hr : r ≠ 0) :
    deriv (deriv fun s => sbessel l (p * s) / s ^ l) r
        + ((2 + 2 * (l : ℝ)) / r) * deriv (fun s => sbessel l (p * s) / s ^ l) r
      = -(p ^ 2) * (sbessel l (p * r) / r ^ l) := by sorry
