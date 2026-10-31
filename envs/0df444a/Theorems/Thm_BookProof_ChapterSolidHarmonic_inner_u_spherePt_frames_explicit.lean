-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonic_inner_u_spherePt_frames_explicit
-- name    : BookProof.ChapterSolidHarmonic.inner_u_spherePt_frames_explicit
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T08:20:46.169319+00:00
-- url     : https://prove2.me/theorems/b324961a-dc5e-4e3e-83b2-7e69629df4dd
-- title:
--   The first frame axis: $\langle u, \mathrm{spherePt}\rangle = r\sin\theta\cos\varphi$
-- statement:
--   For an orthonormal frame $u, v, e$ of a real inner product space,
--   $$\langle u, \mathrm{spherePt}(u,v,e,r,\theta,\varphi)\rangle = r\,\sin\theta\,\cos\varphi ,$$
--   the first Cartesian coordinate of the point of radius $r$ at colatitude $\theta$ and azimuth $\varphi$.
--
--   This is one of the three coordinate projections that turn the abstract sphere integral into the familiar $r^2\sin\theta\,dr\,d\theta\,d\varphi$ integral.
--
--   Corrected statement of the retired node `BookProof.ChapterSolidHarmonic.inner_u_spherePt`; the orthonormality hypotheses are now explicit binders instead of section variables that the export dropped.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/main/BookProof/ChapterSolidHarmonic.lean

-- Corrected statement of BookProof.ChapterSolidHarmonic.inner_u_spherePt.
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

theorem BookProof.ChapterSolidHarmonic.inner_u_spherePt_frames_explicit (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (he : ‖e‖ = 1) (huv : ⟪u, v⟫_ℝ = 0) (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0) (r θ φ : ℝ) : ⟪u, spherePt u v e r θ φ⟫_ℝ = r * Real.sin θ * Real.cos φ := by sorry
