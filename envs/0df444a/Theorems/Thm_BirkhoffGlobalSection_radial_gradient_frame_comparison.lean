-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_radial_gradient_frame_comparison
-- name    : BirkhoffGlobalSection.radial_gradient_frame_comparison
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-29T19:35:42.200201+00:00
-- url     : https://prove2.me/theorems/648ea83d-0994-4bc8-a17a-b6f88989648d
-- title:
--   Positive angular comparison of the radial contact and gradient frames
-- statement:
--   Let $G$ be $C^2$ along a continuous closed path $x(t)$, with $dG_{x(t)}(x(t))>0$. Assume its canonical radial frames $F(t)$ are continuous and symplectic. Then there is a continuous closed family $A(t)$ of real-linear maps of the complex plane with strictly positive angular cross product. For every tangent vector $w\in\ker dG_{x(t)}$, the gradient-frame transverse coordinates $C_t(w)$ satisfy
--
--   $$C_t(w)=A(t)\left((F(t)^{-1}\,\mathrm{toHryn}(w))_2+i(F(t)^{-1}\,\mathrm{toHryn}(w))_3\right),\qquad \operatorname{Im}(\overline z A(t)z)>0\quad(z\ne0).$$
--
--   The family closes whenever the underlying path closes. This comparison identifies the two transverse trivializations while controlling the argument continuously.
-- source:
--   Derived algebraic frame-comparison lemma for BirkhoffGlobalSection.radial_contact_transverse_angle_conjugacy, https://prove2.me/theorems/eab3aa7c-2cfb-4515-b659-4ccc36142c64; uses the exact canonical radial frame and transverse gradient-frame definitions in that theorem. Quaternionic symplectic-frame algebra adapted with credit to Mazecto accepted submission 893234ef-5ec2-4f4b-b415-f79ec1030002. The positive cross-product identity is derived here.

import Mathlib
import Definitions.Def_BirkhoffGlobalSection_CanonicalPositiveFrame
open BirkhoffGlobalSection HryniewiczCriterion
open scoped ContDiff

theorem BirkhoffGlobalSection.radial_gradient_frame_comparison (G : Phase → ℝ) (x : ℝ → Phase) (T : ℝ)
    (hxc : Continuous x) (hG : ∀ t, ContDiffAt ℝ 2 G (x t))
    (hr : ∀ t, 0 < fderiv ℝ G (x t) (x t)) (hperiod : x T = x 0)
    (hFsp : ∀ t, (canonicalRadialFrame G x t).transpose * omegaMat *
      canonicalRadialFrame G x t = omegaMat)
    (hFc : ∀ i j, Continuous fun t => canonicalRadialFrame G x t i j) :
    ∃ A : ℝ → (ℂ →L[ℝ] ℂ), Continuous A ∧ A T = A 0 ∧
      (∀ t z, z ≠ 0 → 0 < (star z * A t z).im) ∧
      (∀ t w, fderiv ℝ G (x t) w = 0 →
        (⟨transverseFrameCoordinates (TangentialHessian.grad G (x t)) w 0,
           transverseFrameCoordinates (TangentialHessian.grad G (x t)) w 1⟩ : ℂ) =
        A t ⟨((canonicalRadialFrame G x t)⁻¹.mulVec (toHryn w)) 2,
             ((canonicalRadialFrame G x t)⁻¹.mulVec (toHryn w)) 3⟩) := by sorry
