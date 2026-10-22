-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_weighted_radial_contact_exterior_derivative
-- name    : BirkhoffGlobalSection.weighted_radial_contact_exterior_derivative
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-30T19:50:22.925986+00:00
-- url     : https://prove2.me/theorems/f6ccc759-0b2f-4327-98c3-bef95bd6f8e9
-- title:
--   Exterior derivative of a weighted radial contact primitive
-- statement:
--   On real four-dimensional phase space use the standard symplectic form omega and the primitive alpha_x(v)=-omega(x,v)/2. If a real-valued weight f is differentiable at u, the antisymmetrized directional derivative of beta=f alpha satisfies, for all ambient vectors v,w,
--
--   $$d\beta_u(v,w)=Df_u(v)\alpha_u(w)-Df_u(w)\alpha_u(v)-f(u)\omega(v,w).$$
--
--   The formal assertion writes the exterior derivative explicitly as directional derivatives along constant ambient vector fields. In particular, the derivative-of-weight terms vanish when both vectors lie in the contact plane.
-- source:
--   Auxiliary coordinate formulation of Hryniewicz, arXiv:1105.2077v5, p. 1 contact-volume definition and p. 2 star-shaped primitive pullback, https://arxiv.org/pdf/1105.2077, in the workspace convention alpha=-omega(x,.)/2. This is an explicit auxiliary result, not a verbatim source theorem.

import Definitions.Def_BirkhoffGlobalSection_TransverseHopf
import Mathlib.Analysis.Calculus.FDeriv.Mul

open scoped ContDiff Topology
open BirkhoffGlobalSection Set

theorem BirkhoffGlobalSection.weighted_radial_contact_exterior_derivative (f : Phase → ℝ)
    (u v w : Phase) (hf : DifferentiableAt ℝ f u) :
    fderiv ℝ (fun x => f x * phaseRadialContact x w) u v -
      fderiv ℝ (fun x => f x * phaseRadialContact x v) u w =
    fderiv ℝ f u v * phaseRadialContact u w -
      fderiv ℝ f u w * phaseRadialContact u v - f u * phaseSymplecticForm v w := by sorry
