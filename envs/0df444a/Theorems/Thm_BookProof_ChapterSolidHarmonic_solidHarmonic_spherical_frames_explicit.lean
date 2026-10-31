-- Prove2me | Theorems.Thm_BookProof_ChapterSolidHarmonic_solidHarmonic_spherical_frames_explicit
-- name    : BookProof.ChapterSolidHarmonic.solidHarmonic_spherical_frames_explicit
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-30T08:20:44.683988+00:00
-- url     : https://prove2.me/theorems/7cec10b6-01ba-4158-8501-e507184b4843
-- title:
--   Spherical form of a solid harmonic: $\mathrm{solidHarmonic}(x) = r^{l}\,P_{l}^{\mu}(\cos\theta)\cos(\mu\varphi)$
-- statement:
--   For an orthonormal frame $u, v, e$, a multi-index $\mu \le l$, a radius $r > 0$, a colatitude with $\sin\theta \ge 0$ and any azimuth $\varphi$,
--   $$\mathrm{solidHarmonic}_{l,\mu}(\mathrm{spherePt}(u,v,e,r,\theta,\varphi)) = r^{l}\,P_{l}^{\mu}(\cos\theta)\,\cos(\mu\varphi),$$
--   where $P_{l}^{\mu}$ is the associated Legendre function.
--
--   This is the separation-of-variables identity for solid harmonics: a homogeneous harmonic polynomial of degree $l$ restricts to the sphere as a spherical harmonic, and its radial dependence is the factor $r^{l}$.  It is the bridge between the abstract polynomial definition of `solidHarmonic` and the classical spherical-harmonic expansion used in the multipole arguments of the book.
--
--   Corrected statement of the retired node `BookProof.ChapterSolidHarmonic.solidHarmonic_spherical`, whose exported target had lost the frame hypotheses; they are explicit binders here.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/main/BookProof/ChapterSolidHarmonic.lean

-- Corrected statement of BookProof.ChapterSolidHarmonic.solidHarmonic_spherical.
-- The retired node's target silently dropped the hypothesis this statement needs
-- (see its description); here the hypothesis is an explicit binder of the theorem
-- below, so a re-export cannot lose it.  Source of record:
-- timepiece/BookProof/ChapterSolidHarmonic.lean (Lean 4.28) and timepiece331/BookProof/ChapterSolidHarmonic.lean (Lean 4.33.1).
import Definitions.Def_ChapterRadialLaplacian
import Definitions.Def_ChapterLaplacianProduct
import Definitions.Def_ChapterSolidHarmonicTools
import Mathlib
import Definitions.Def_ChapterSolidHarmonic
import Definitions.Def_ChapterLegendrePolynomial
open BookProof.ChapterLegendrePolynomial
open BookProof.ChapterSolidHarmonic



open Laplacian InnerProductSpace Polynomial
open BookProof.ChapterRadialLaplacian BookProof.ChapterLaplacianProduct
open BookProof.ChapterSolidHarmonicTools BookProof.ChapterLegendrePolynomial
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {u v e : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (he : ‖e‖ = 1)
  (huv : ⟪u, v⟫_ℝ = 0) (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0)

theorem BookProof.ChapterSolidHarmonic.solidHarmonic_spherical_frames_explicit (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (he : ‖e‖ = 1) (huv : ⟪u, v⟫_ℝ = 0) (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0) {l μ : ℕ} (hμ : μ ≤ l) {r : ℝ} (hr : 0 < r) {θ : ℝ} (hθ : 0 ≤ Real.sin θ) (φ : ℝ) : solidHarmonic u v e l μ (spherePt u v e r θ φ) = r ^ l * assocLegendre l μ (Real.cos θ) * Real.cos (μ * φ) := by sorry
