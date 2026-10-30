-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_strict_convex_orbit_positive_canonical_model
-- name    : BirkhoffGlobalSection.strict_convex_orbit_positive_canonical_model
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-29T17:08:59.352527+00:00
-- url     : https://prove2.me/theorems/55100510-e824-4da4-8931-8673d294fb84
-- title:
--   Local positive canonical model along a tangentially convex orbit
-- statement:
--   Let $G$ have two continuous derivatives and a positive tangential Hessian at every point of a closed Hamiltonian orbit $x(t)$ of period $T>0$, with $dG(x(t))x(t)>0$. Let $Y(t)$ be the variational flow with $Y(0)=I$. Let $F(t)$ be the canonical radial contact frame and let $\varphi$ be the lower transverse block of $F(\tau T)^{-1}Y(\tau T)F(0)$ in the fixed symplectic coordinate convention.
--
--   Then $(F,\varphi,T)$ is a positive moving frame. In particular, there is a continuous symmetric positive definite generator $S(t)$ with
--
--   $$\frac{d}{dt}\left[F(0)^{-1}F(t)\operatorname{diag}(I,\varphi(t/T))\right]
--   =JS(t)F(0)^{-1}F(t)\operatorname{diag}(I,\varphi(t/T)).$$
--
--   The conclusion also includes symplecticity and periodicity of $F$, its canonical determinant half-plane condition, and continuity, determinant one, and initial identity of $\varphi$. This is the geometric construction needed to apply the positive-path winding estimate locally, without a globally homogeneous Hamiltonian. It is an open construction obligation; no winding bound is assumed.
-- source:
--   Derived local refinement of the HWZ frame argument, Ann. Math.148(1998), equations(3.33)-(3.46), https://doi.org/10.2307/120994; global homogeneous frame-flow source: https://prove2.me/theorems/6eddbaa1-2e75-45c3-8798-b233d355f366. Quaternionic gradient frame convention: Joung-van Koert Section2.3, https://arxiv.org/html/2407.19159v3. These are explicitly identified local derived obligations, not verbatim numbered statements.

import Definitions.Def_BirkhoffGlobalSection_CanonicalPositiveFrame
import Definitions.Def_BirkhoffGlobalSection_RegularizationModel
open BirkhoffGlobalSection HryniewiczCriterion

theorem BirkhoffGlobalSection.strict_convex_orbit_positive_canonical_model
    (G : Phase → ℝ) (x : ℝ → Phase) (T : ℝ)
    (hx : IsPeriodicHamiltonianSolutionIn G {y | IsStrictlyConvexStarShapedAt G y} x T)
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY0 : Y 0 = ContinuousLinearMap.id ℝ Phase)
    (hY : ∀ t : ℝ, HasDerivAt Y
      ((fderiv ℝ (hamiltonianVectorField G) (x t)).comp (Y t)) t) :
    IsPositiveMovingFrame (canonicalRadialFrame G x) (canonicalTransversePath G x T Y) T := by sorry
