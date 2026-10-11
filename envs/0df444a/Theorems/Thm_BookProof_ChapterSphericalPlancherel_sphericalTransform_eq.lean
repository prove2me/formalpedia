-- Prove2me | Theorems.Thm_BookProof_ChapterSphericalPlancherel_sphericalTransform_eq
-- name    : BookProof.ChapterSphericalPlancherel.sphericalTransform_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:21:35.429678+00:00
-- url     : https://prove2.me/theorems/4deba1a8-bf43-47b0-8775-a86bb47ebd0c
-- title:
--   `BookProof.ChapterSphericalPlancherel.sphericalTransform_eq` {f : ℝ → ℂ} {G : ℝ → ℂ} (hf : ∀ r ∈ Ioi (0 : ℝ), (r : ℂ) * f r = G r) {p : ℝ} (hp : 0 < p) : sphericalTransform...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSphericalPlancherel`.
--
--   `BookProof.ChapterSphericalPlancherel.sphericalTransform_eq` {f : ℝ → ℂ} {G : ℝ → ℂ} (hf : ∀ r ∈ Ioi (0 : ℝ), (r : ℂ) * f r = G r) {p : ℝ} (hp : 0 < p) : sphericalTransform f p = (Real.sqrt (2 / π) : ℂ) * ((p : ℂ)⁻¹ * sineKernelTransform G p)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSphericalPlancherel.sphericalTransform_eq`.

-- Generated from ChapterSphericalPlancherel.lean — theorem BookProof.ChapterSphericalPlancherel.sphericalTransform_eq
import Mathlib
import Definitions.Def_ChapterSphericalPlancherel
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBessel
open BookProof.ChapterSphericalPlancherel



open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

theorem BookProof.ChapterSphericalPlancherel.sphericalTransform_eq {f : ℝ → ℂ} {G : ℝ → ℂ}
    (hf : ∀ r ∈ Ioi (0 : ℝ), (r : ℂ) * f r = G r) {p : ℝ} (hp : 0 < p) :
    sphericalTransform f p
      = (Real.sqrt (2 / π) : ℂ) * ((p : ℂ)⁻¹ * sineKernelTransform G p) := by sorry
