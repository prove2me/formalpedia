-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_boundary_sphere_contact_volume
-- name    : BirkhoffGlobalSection.convex_boundary_sphere_contact_volume
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-30T20:11:51.136778+00:00
-- url     : https://prove2.me/theorems/edca862b-0d1a-4f1f-9697-eedc1da40a33
-- title:
--   The inverse chart of a smooth convex boundary has positive sphere contact volume
-- statement:
--   Let B be a convex, von Neumann bounded neighborhood of zero in four-dimensional real phase space. Let F vanish on its frontier, be smooth at every frontier point, and satisfy DF_y(y) nonzero there. Put G(u)=g_B(u)^{-1}u and f(u)=Q(G(u)), with Q the coordinate squared radius. At every unit-sphere point u, three sphere-tangent vectors r,v,w satisfy
--
--   $$((f\alpha)\wedge d(f\alpha))_u(r,v,w)>0.$$
--
--   The exterior derivative is written explicitly using ambient directional derivatives. The previously proved smooth gauge chart and positive-weight pullback supply the chart and weight hypotheses. This is the sphere contact-volume step of the boundary-to-sphere correspondence; a complete Reeb clock and dynamical convexity require further results.
-- source:
--   Auxiliary coordinate formulation of Hryniewicz, arXiv:1105.2077v5, p. 1 contact-volume definition and p. 2 star-shaped primitive pullback, https://arxiv.org/pdf/1105.2077, in the workspace convention alpha=-omega(x,.)/2. This is an explicit auxiliary result, not a verbatim source theorem.

import Theorems.Thm_BirkhoffGlobalSection_smooth_radial_gauge_chart
import Theorems.Thm_BirkhoffGlobalSection_gauge_inverse_contact_weight

open scoped ContDiff Topology
open BirkhoffGlobalSection Set

theorem BirkhoffGlobalSection.convex_boundary_sphere_contact_volume (B : Set Phase) (hc : Convex ℝ B)
    (h0 : B ∈ 𝓝 (0 : Phase)) (hb : Bornology.IsVonNBounded ℝ B) (F : Phase → ℝ)
    (hzero : ∀ y ∈ frontier B, F y = 0)
    (hsmooth : ∀ y ∈ frontier B, ContDiffAt ℝ ∞ F y)
    (hrad : ∀ y ∈ frontier B, fderiv ℝ F y y ≠ 0)
    (u : Phase) (hu : u ∈ unitThreeSphere) :
    let G : Phase → Phase := fun x => (gauge B x)⁻¹ • x
    let f : Phase → ℝ := fun x => zNormSq (G x) + wNormSq (G x)
    let d : Phase → Phase → ℝ := fun v w =>
      fderiv ℝ (fun x => f x * phaseRadialContact x w) u v -
        fderiv ℝ (fun x => f x * phaseRadialContact x v) u w
    ∃ r v w : Phase,
      (u 0 * r 0 + u 1 * r 1 + u 2 * r 2 + u 3 * r 3 = 0) ∧
      (u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0) ∧
      (u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0) ∧
      0 < f u * phaseRadialContact u r * d v w -
        f u * phaseRadialContact u v * d r w +
        f u * phaseRadialContact u w * d r v := by sorry
