-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonic_inner_v_spherePt_frames_explicit
-- name    : BookProof.ChapterSolidHarmonic.inner_v_spherePt_frames_explicit
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T08:20:44.26181+00:00
-- url     : https://prove2.me/theorems/a6510aa5-7e35-487c-833d-8d9cafa604c4
-- title:
--   The second frame axis: $\langle v, \mathrm{spherePt}\rangle = r\sin\theta\sin\varphi$
-- statement:
--   On the unit sphere in a real inner product space, parametrised by an orthonormal frame $u, v, e$ and spherical angles,
--   $$\langle v, \mathrm{spherePt}(u,v,e,r,\theta,\varphi)\rangle = r\,\sin\theta\,\sin\varphi .$$
--
--   Together with the two companion identities for $u$ and $e$ this is the change of variables from the abstract sphere to the classical angle coordinates: the three inner products against the frame are the three Cartesian coordinates of the point.  The frame hypothesis — unit vectors, pairwise orthogonal — is what makes the coordinate functions orthogonal coordinates.
--
--   Corrected statement of the retired node `BookProof.ChapterSolidHarmonic.inner_v_spherePt`.  The frame conditions `hu hv he huv hue hve` were section `variable`s that did not occur in the type, so Lean dropped them and the published target quantified over arbitrary, possibly non-orthonormal vectors; they are now explicit binders of the statement.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/main/BookProof/ChapterSolidHarmonic.lean

-- Corrected statement of BookProof.ChapterSolidHarmonic.inner_v_spherePt.
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

theorem BookProof.ChapterSolidHarmonic.inner_v_spherePt_frames_explicit (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (he : ‖e‖ = 1) (huv : ⟪u, v⟫_ℝ = 0) (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0) (r θ φ : ℝ) : ⟪v, spherePt u v e r θ φ⟫_ℝ = r * Real.sin θ * Real.sin φ := by sorry
