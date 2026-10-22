-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_weighted_sphere_contact_geometry
-- name    : BirkhoffGlobalSection.weighted_sphere_contact_geometry
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-30T20:09:34.361924+00:00
-- url     : https://prove2.me/theorems/d5b895e8-6b3a-441c-b09f-b878c24eaa22
-- title:
--   Positive weighted sphere primitives satisfy the contact condition
-- statement:
--   Let u lie on the coordinate Euclidean unit three-sphere, and let f be a real-valued ambient function differentiable at u with f(u)>0. Set beta=f alpha, where alpha_x(v)=-omega(x,v)/2. The sphere tangent space is given by the equation dot(u,v)=0. Then beta is nonzero on this tangent space, and d beta has trivial kernel on its contact plane. Moreover, three tangent vectors r,v,w can be chosen so that
--
--   $$(\beta\wedge d\beta)_u(r,v,w)>0.$$
--
--   Here d beta is the actual antisymmetrized ambient derivative restricted to tangent vectors. This establishes the pointwise contact condition; it makes no assertion about periodic Reeb orbit nondegeneracy.
-- source:
--   Auxiliary coordinate formulation of Hryniewicz, arXiv:1105.2077v5, p. 1 contact-volume definition and p. 2 star-shaped primitive pullback, https://arxiv.org/pdf/1105.2077, in the workspace convention alpha=-omega(x,.)/2. This is an explicit auxiliary result, not a verbatim source theorem.

import Theorems.Thm_BirkhoffGlobalSection_weighted_radial_contact_exterior_derivative

open scoped ContDiff Topology
open BirkhoffGlobalSection Set

theorem BirkhoffGlobalSection.weighted_sphere_contact_geometry (f : Phase → ℝ) (u : Phase)
    (hu : u ∈ unitThreeSphere) (hf : 0 < f u) (hdf : DifferentiableAt ℝ f u) :
    ((∃ r : Phase,
      u 0 * r 0 + u 1 * r 1 + u 2 * r 2 + u 3 * r 3 = 0 ∧
      f u * phaseRadialContact u r ≠ 0) ∧
    (∀ v : Phase,
      u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0 →
      f u * phaseRadialContact u v = 0 →
      (∀ w : Phase,
        u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
        f u * phaseRadialContact u w = 0 →
        fderiv ℝ (fun x => f x * phaseRadialContact x w) u v -
          fderiv ℝ (fun x => f x * phaseRadialContact x v) u w = 0) → v = 0)) ∧
    (let d : Phase → Phase → ℝ := fun v w =>
      fderiv ℝ (fun x => f x * phaseRadialContact x w) u v -
        fderiv ℝ (fun x => f x * phaseRadialContact x v) u w
    ∃ r v w : Phase,
      (u 0 * r 0 + u 1 * r 1 + u 2 * r 2 + u 3 * r 3 = 0) ∧
      (u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0) ∧
      (u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0) ∧
      0 < f u * phaseRadialContact u r * d v w -
        f u * phaseRadialContact u v * d r w +
        f u * phaseRadialContact u w * d r v) := by sorry
