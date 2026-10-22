-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_gauge_inverse_contact_pullback
-- name    : BirkhoffGlobalSection.gauge_inverse_contact_pullback
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-30T18:28:29.926962+00:00
-- url     : https://prove2.me/theorems/5d2fa334-b401-4af2-9dd6-7a4190cb6b8f
-- title:
--   The inverse radial gauge chart pulls back the contact primitive
-- statement:
--   Let B be any subset of real four-dimensional phase space, let u lie on the coordinate Euclidean unit sphere, and suppose the inverse radial gauge map G(x)=g_B(x)^{-1}x is smooth at u. Write Q(y) for the sum of the squares of its four coordinates and alpha_y(v) for the radial contact primitive used in this workspace. Then, for every ambient vector v,
--
--   $$\alpha_{G(u)}(DG_u v)=Q(G(u))\,\alpha_u(v).$$
--
--   Thus the inverse map pulls back the primitive with weight equal to the squared radius of its image. Smoothness is an explicit hypothesis, supplied in convex-boundary applications by the published smooth radial gauge chart. No positivity of this weight is asserted for arbitrary B. Contact nondegeneracy, complete Reeb dynamics and global sections require further arguments.
-- source:
--   Auxiliary explicit inverse-gauge version of the star-shaped primitive pullback discussed in Hryniewicz, arXiv:1105.2077v5, p. 2, https://arxiv.org/pdf/1105.2077, translated to the workspace radial primitive convention. Uses the proved BirkhoffGlobalSection.radial_rescaling_contact_pullback (37bf7bc6-4d14-48b7-9e50-6610d9d83f52). The smoothness hypothesis is explicit; this is not a verbatim source theorem.

import Mathlib.Analysis.Convex.Gauge
import Theorems.Thm_BirkhoffGlobalSection_radial_rescaling_contact_pullback
open scoped ContDiff Topology
open BirkhoffGlobalSection Filter Set

theorem BirkhoffGlobalSection.gauge_inverse_contact_pullback (B : Set Phase) (u v : Phase)
    (hu : u ∈ unitThreeSphere)
    (hG : ContDiffAt ℝ ∞ (fun x : Phase => (gauge B x)⁻¹ • x) u) :
    let G : Phase → Phase := fun x => (gauge B x)⁻¹ • x
    phaseRadialContact (G u) (fderiv ℝ G u v) =
      (zNormSq (G u) + wNormSq (G u)) * phaseRadialContact u v := by sorry
