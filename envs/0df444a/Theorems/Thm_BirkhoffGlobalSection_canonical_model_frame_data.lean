-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_canonical_model_frame_data
-- name    : BirkhoffGlobalSection.canonical_model_frame_data
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-29T17:18:28.186346+00:00
-- url     : https://prove2.me/theorems/ce6c9e48-01a8-4c9d-8c5d-23889243249a
-- title:
--   Symplecticity, continuity and normalization of the canonical orbit frame
-- statement:
--   Let $G$ be a Hamiltonian and let $x(t)$ be a closed orbit of positive closing time $T$, lying at strictly convex star-shaped points where $G$ is $C^2$. Let $Y(t)$ be its variational flow, initially the identity. Write $F(t)$ for the canonical radial contact frame and $\varphi$ for the lower transverse block of $F(\tau T)^{-1}Y(\tau T)F(0)$ in the fixed symplectic coordinates.
--
--   The frame and transverse block satisfy the following six conditions:
--
--   1. $F(t)^\top\Omega F(t)=\Omega$.
--   2. $\operatorname{Re}(i\,d(F(t)))>0$, where $d$ is the complex-linear determinant.
--   3. Every matrix entry of $F(t)$ is continuous.
--   4. $F(T)=F(0)$.
--   5. Every matrix entry of $\varphi$ is continuous on $[0,1]$.
--   6. $\varphi(0)=I$.
--
--   These are the frame, regularity and initial-value conditions of the local positive canonical model. Determinant one of the transverse block and positivity of its completed generator are separate assertions.
-- source:
--   Derived local frame conditions for BirkhoffGlobalSection.strict_convex_orbit_positive_canonical_model, https://prove2.me/theorems/55100510-e824-4da4-8931-8673d294fb84. Generic symplectic frame and complex determinant algebra adapted with credit to Mazecto, accepted submission893234ef-5ec2-4f4b-b415-f79ec1030002, https://prove2.me/theorems/f880a9bf-1521-4b02-a828-1c90ceda0bb1. HWZ Ann.Math.148(1998), equations(3.35)-(3.39), https://doi.org/10.2307/120994. The C2 along-orbit and coordinate statements are derived here, not verbatim source assertions.

import Definitions.Def_BirkhoffGlobalSection_CanonicalPositiveFrame
import Definitions.Def_BirkhoffGlobalSection_RegularizationModel
open BirkhoffGlobalSection HryniewiczCriterion

theorem BirkhoffGlobalSection.canonical_model_frame_data (G : Phase → ℝ) (x : ℝ → Phase) (T : ℝ)
    (hx : IsPeriodicHamiltonianSolutionIn G {y | IsStrictlyConvexStarShapedAt G y} x T)
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY0 : Y 0 = ContinuousLinearMap.id ℝ Phase)
    (hY : ∀ t : ℝ, HasDerivAt Y
      ((fderiv ℝ (BirkhoffGlobalSection.hamiltonianVectorField G) (x t)).comp (Y t)) t) :
    (∀ t, (canonicalRadialFrame G x t).transpose * omegaMat *
      canonicalRadialFrame G x t = omegaMat) ∧
    (∀ t, 0 < (Complex.I * cdet (canonicalRadialFrame G x t)).re) ∧
    (∀ i j, Continuous fun t => canonicalRadialFrame G x t i j) ∧
    (canonicalRadialFrame G x T = canonicalRadialFrame G x 0) ∧
    (∀ i j, ContinuousOn (fun τ => canonicalTransversePath G x T Y τ i j) (Set.Icc 0 1)) ∧
    canonicalTransversePath G x T Y 0 = 1 := by sorry
