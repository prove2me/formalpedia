-- Prove2me | Theorems.Thm_BookProof_ChapterBesselHarmonic_hasDerivAt_quot
-- name    : BookProof.ChapterBesselHarmonic.hasDerivAt_quot
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:54:46.03899+00:00
-- url     : https://prove2.me/theorems/df9dbfc3-4a75-419d-8b5a-1a0002c7142a
-- title:
--   `BookProof.ChapterBesselHarmonic.hasDerivAt_quot` {R : ℝ → ℝ} {l : ℕ} {s : ℝ} (hs : s ≠ 0) (hR : DifferentiableAt ℝ R s) : HasDerivAt (fun t => R t / t ^ l) (deriv R s / s ^ l - (l
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBesselHarmonic`.
--
--   `BookProof.ChapterBesselHarmonic.hasDerivAt_quot` {R : ℝ → ℝ} {l : ℕ} {s : ℝ} (hs : s ≠ 0) (hR : DifferentiableAt ℝ R s) : HasDerivAt (fun t => R t / t ^ l) (deriv R s / s ^ l - (l : ℝ) * R s / s ^ (l + 1)) s
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBesselHarmonic.hasDerivAt_quot`.

-- Generated from ChapterBesselHarmonic.lean — theorem BookProof.ChapterBesselHarmonic.hasDerivAt_quot
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

theorem BookProof.ChapterBesselHarmonic.hasDerivAt_quot {R : ℝ → ℝ} {l : ℕ} {s : ℝ} (hs : s ≠ 0) (hR : DifferentiableAt ℝ R s) :
    HasDerivAt (fun t => R t / t ^ l)
      (deriv R s / s ^ l - (l : ℝ) * R s / s ^ (l + 1)) s := by sorry
