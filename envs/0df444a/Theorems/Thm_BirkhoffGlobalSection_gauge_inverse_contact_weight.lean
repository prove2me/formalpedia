-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_gauge_inverse_contact_weight
-- name    : BirkhoffGlobalSection.gauge_inverse_contact_weight
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-30T19:50:01.6853+00:00
-- url     : https://prove2.me/theorems/6b41fd87-7a7f-4ee8-b4b5-ae8624f5ca3c
-- title:
--   The inverse radial gauge chart has a positive smooth contact weight
-- statement:
--   Let B be a von Neumann bounded neighborhood of zero in real four-dimensional phase space, let u be a coordinate Euclidean unit-sphere point, and assume the inverse gauge map G(x)=g_B(x)^{-1}x is smooth at u. For Q(y) equal to the sum of four coordinate squares, put f(x)=Q(G(x)). Then f is smooth at u and f(u)>0, and for every ambient vector v,
--
--   $$\alpha_{G(u)}(DG_u v)=f(u)\alpha_u(v).$$
--
--   Thus the inverse radial chart transports the boundary primitive to a positive smooth multiple of the standard sphere primitive. Convexity is unnecessary for this assertion; smoothness of G remains an explicit hypothesis.
-- source:
--   Auxiliary coordinate formulation of Hryniewicz, arXiv:1105.2077v5, p. 1 contact-volume definition and p. 2 star-shaped primitive pullback, https://arxiv.org/pdf/1105.2077, in the workspace convention alpha=-omega(x,.)/2. This is an explicit auxiliary result, not a verbatim source theorem.

import Mathlib.Analysis.Convex.Gauge
import Theorems.Thm_BirkhoffGlobalSection_gauge_inverse_contact_pullback

open scoped ContDiff Topology
open BirkhoffGlobalSection Set

theorem BirkhoffGlobalSection.gauge_inverse_contact_weight (B : Set Phase) (h0 : B ∈ 𝓝 (0 : Phase))
    (hb : Bornology.IsVonNBounded ℝ B) (u : Phase) (hu : u ∈ unitThreeSphere)
    (hG : ContDiffAt ℝ ∞ (fun x : Phase => (gauge B x)⁻¹ • x) u) :
    let G : Phase → Phase := fun x => (gauge B x)⁻¹ • x
    let f : Phase → ℝ := fun x => zNormSq (G x) + wNormSq (G x)
    0 < f u ∧ ContDiffAt ℝ ∞ f u ∧
      (∀ v : Phase, phaseRadialContact (G u) (fderiv ℝ G u v) =
        f u * phaseRadialContact u v) := by sorry
