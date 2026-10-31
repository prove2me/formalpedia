-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonic_norm_spherePt_frames_explicit
-- name    : BookProof.ChapterSolidHarmonic.norm_spherePt_frames_explicit
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T08:20:43.926149+00:00
-- url     : https://prove2.me/theorems/f0d95bb9-9d4e-460f-a00e-24b3272c4186
-- title:
--   The sphere parametrisation has norm $r$
-- statement:
--   For an orthonormal frame $u, v, e$, a radius $r \ge 0$ and any angles $\theta, \varphi$,
--   $$\|\mathrm{spherePt}(u,v,e,r,\theta,\varphi)\| = r .$$
--
--   So the map $(r,\theta,\varphi) \mapsto \mathrm{spherePt}$ lands on the sphere of radius $r$; combined with the three inner-product identities it is a bijection onto that sphere away from the poles.  The hypothesis $r \ge 0$ is essential (the norm is non-negative) and is part of the statement.
--
--   Corrected statement of the retired node `BookProof.ChapterSolidHarmonic.norm_spherePt`; the normality of the frame was a section variable that the export dropped and is now an explicit binder.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/main/BookProof/ChapterSolidHarmonic.lean

-- Corrected statement of BookProof.ChapterSolidHarmonic.norm_spherePt.
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

theorem BookProof.ChapterSolidHarmonic.norm_spherePt_frames_explicit (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (he : ‖e‖ = 1) (huv : ⟪u, v⟫_ℝ = 0) (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0) {r : ℝ} (hr : 0 ≤ r) (θ φ : ℝ) : ‖spherePt u v e r θ φ‖ = r := by sorry
