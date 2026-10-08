-- Prove2me | Theorems.Thm_BookProof_ChapterBesselHarmonic_reduced_from_radial
-- name    : BookProof.ChapterBesselHarmonic.reduced_from_radial
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:54:58.722853+00:00
-- url     : https://prove2.me/theorems/1655fffd-6ddc-4e4c-b436-3d6303437ff9
-- title:
--   `BookProof.ChapterBesselHarmonic.reduced_from_radial` {R : ℝ → ℝ} {l : ℕ} {p r : ℝ} (hr : r ≠ 0) (hR : DifferentiableAt ℝ R r) (hR' : DifferentiableAt ℝ (deriv R) r) (hRev : ∀ᶠ s i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBesselHarmonic`.
--
--   `BookProof.ChapterBesselHarmonic.reduced_from_radial` {R : ℝ → ℝ} {l : ℕ} {p r : ℝ} (hr : r ≠ 0) (hR : DifferentiableAt ℝ R r) (hR' : DifferentiableAt ℝ (deriv R) r) (hRev : ∀ᶠ s in nhds r, DifferentiableAt ℝ R s) (hode : deriv (deriv R) r + (2 / r) * deriv R r + (p ^ 2 - (l : ℝ) * (l + 1) / r ^ 2) * R r = 0) : deriv (deriv fun s => R s / s ^ l) r + ((2 + 2 * (l : ℝ)) / r) * deriv (fun s => R s / s ^ l) r = -(p ^ 2) * (R r / r ^ l)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBesselHarmonic.reduced_from_radial`.

-- Generated from ChapterBesselHarmonic.lean — theorem BookProof.ChapterBesselHarmonic.reduced_from_radial
import Definitions.Def_ChapterSphericalBessel
import Definitions.Def_ChapterSphericalBesselODE
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
import Mathlib
import Definitions.Def_ChapterBesselHarmonic
open BookProof.ChapterBesselHarmonic



open Filter Laplacian InnerProductSpace
open BookProof.ChapterSphericalBessel BookProof.ChapterSphericalBesselODE
open BookProof.ChapterRadialLaplacian BookProof.ChapterLaplacianProduct
open scoped InnerProductSpace RealInnerProductSpace

theorem BookProof.ChapterBesselHarmonic.reduced_from_radial {R : ℝ → ℝ} {l : ℕ} {p r : ℝ} (hr : r ≠ 0)
    (hR : DifferentiableAt ℝ R r) (hR' : DifferentiableAt ℝ (deriv R) r)
    (hRev : ∀ᶠ s in nhds r, DifferentiableAt ℝ R s)
    (hode : deriv (deriv R) r + (2 / r) * deriv R r
      + (p ^ 2 - (l : ℝ) * (l + 1) / r ^ 2) * R r = 0) :
    deriv (deriv fun s => R s / s ^ l) r
        + ((2 + 2 * (l : ℝ)) / r) * deriv (fun s => R s / s ^ l) r
      = -(p ^ 2) * (R r / r ^ l) := by sorry
