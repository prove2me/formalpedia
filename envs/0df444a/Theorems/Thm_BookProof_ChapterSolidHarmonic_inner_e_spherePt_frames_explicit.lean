-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonic_inner_e_spherePt_frames_explicit
-- name    : BookProof.ChapterSolidHarmonic.inner_e_spherePt_frames_explicit
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T08:20:48.697614+00:00
-- url     : https://prove2.me/theorems/2a95a67d-d514-43e9-90bc-3c2f71fdba32
-- title:
--   The third frame axis: $\langle e, \mathrm{spherePt}\rangle = r\cos\theta$
-- statement:
--   For an orthonormal frame $u, v, e$ of a real inner product space,
--   $$\langle e, \mathrm{spherePt}(u,v,e,r,\theta,\varphi)\rangle = r\,\cos\theta ,$$
--   the height of the point above the $u$–$v$ plane.
--
--   It is the coordinate whose $\theta$-dependence involves no azimuth, which is why the Legendre polynomials — functions of $\cos\theta$ alone — appear in the solid-harmonic expansion.
--
--   Corrected statement of the retired node `BookProof.ChapterSolidHarmonic.inner_e_spherePt`, with the frame hypotheses explicit.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/main/BookProof/ChapterSolidHarmonic.lean

-- Corrected statement of BookProof.ChapterSolidHarmonic.inner_e_spherePt.
-- The retired node's target silently dropped the hypothesis this statement needs
-- (see its description); here the hypothesis is an explicit binder of the theorem
-- below, so a re-export cannot lose it.  Source of record:
-- timepiece/BookProof/ChapterSolidHarmonic.lean (Lean 4.28) and timepiece331/BookProof/ChapterSolidHarmonic.lean (Lean 4.33.1).
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
import Definitions.Def_ChapterSolidHarmonicTools
import Definitions.Def_ChapterLegendrePolynomial
import Mathlib
import Definitions.Def_ChapterSolidHarmonic
open BookProof.ChapterSolidHarmonic



open Laplacian InnerProductSpace Polynomial
open BookProof.ChapterRadialLaplacian BookProof.ChapterLaplacianProduct
open BookProof.ChapterSolidHarmonicTools BookProof.ChapterLegendrePolynomial
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {u v e : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (he : ‖e‖ = 1)
  (huv : ⟪u, v⟫_ℝ = 0) (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0)

theorem BookProof.ChapterSolidHarmonic.inner_e_spherePt_frames_explicit (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (he : ‖e‖ = 1) (huv : ⟪u, v⟫_ℝ = 0) (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0) (r θ φ : ℝ) : ⟪e, spherePt u v e r θ φ⟫_ℝ = r * Real.cos θ := by sorry
