-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_radial_contact_transverse_angle_conjugacy
-- name    : BirkhoffGlobalSection.radial_contact_transverse_angle_conjugacy
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-29T17:08:52.031393+00:00
-- url     : https://prove2.me/theorems/eab3aa7c-2cfb-4515-b659-4ccc36142c64
-- title:
--   Endpoint angle conjugacy between radial and gradient frames
-- statement:
--   Use a closed orbit, variational flow, radial contact frame, and transverse path $\varphi$ as in the local positive canonical model. For a nonzero transverse tangent initial vector, let $\theta(t)$ be any continuous polar angle of its variational image in the quaternionic gradient frame.
--
--   There exist an initial angle $s\in[0,2\pi)$, a vector-angle lift $\beta$ of $\varphi$ starting at $s$, and a strictly increasing angular coordinate lift $a:\mathbb R\to\mathbb R$ such that
--
--   $$a(u+2\pi)=a(u)+2\pi,\qquad
--   \theta(T)-\theta(0)=a(\beta(1))-a(s).$$
--
--   This expresses the endpoint change of coordinates as a degree-one orientation-preserving lift. It separates the frame-comparison obligation from the spectral positive-path estimate. The statement requires the same local regularity and star-shaped convexity hypotheses as the orbit model, includes every positive closing time, and assumes no winding inequality.
-- source:
--   Derived local refinement of the HWZ frame argument, Ann. Math.148(1998), equations(3.33)-(3.46), https://doi.org/10.2307/120994; global homogeneous frame-flow source: https://prove2.me/theorems/6eddbaa1-2e75-45c3-8798-b233d355f366. Quaternionic gradient frame convention: Joung-van Koert Section2.3, https://arxiv.org/html/2407.19159v3. These are explicitly identified local derived obligations, not verbatim numbered statements.

import Definitions.Def_BirkhoffGlobalSection_CanonicalPositiveFrame
import Definitions.Def_BirkhoffGlobalSection_RegularizationModel
open BirkhoffGlobalSection HryniewiczCriterion

theorem BirkhoffGlobalSection.radial_contact_transverse_angle_conjugacy
    (G : Phase → ℝ) (x : ℝ → Phase) (T : ℝ)
    (hx : IsPeriodicHamiltonianSolutionIn G {y | IsStrictlyConvexStarShapedAt G y} x T)
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY0 : Y 0 = ContinuousLinearMap.id ℝ Phase)
    (hY : ∀ t : ℝ, HasDerivAt Y
      ((fderiv ℝ (hamiltonianVectorField G) (x t)).comp (Y t)) t)
    (v : Phase) (hv : fderiv ℝ G (x 0) v = 0)
    (hvne : transverseFrameCoordinates (TangentialHessian.grad G (x 0)) v ≠ 0)
    (θ : ℝ → ℝ) (hθc : Continuous θ)
    (hθ : ∀ t : ℝ, ∃ ρ : ℝ, 0 < ρ ∧
      transverseFrameCoordinates (TangentialHessian.grad G (x t)) (Y t v) =
        ![ρ * Real.cos (θ t), ρ * Real.sin (θ t)]) :
    ∃ (s : ℝ) (β a : ℝ → ℝ),
      s ∈ Set.Ico (0 : ℝ) (2 * Real.pi) ∧
      IsAngleLift (canonicalTransversePath G x T Y) s β ∧
      StrictMono a ∧
      (∀ u : ℝ, a (u + 2 * Real.pi) = a u + 2 * Real.pi) ∧
      θ T - θ 0 = a (β 1) - a s := by sorry
