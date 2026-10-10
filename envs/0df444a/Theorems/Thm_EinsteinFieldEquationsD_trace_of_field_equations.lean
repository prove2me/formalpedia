-- Prove2me | Theorems.Thm_EinsteinFieldEquationsD_trace_of_field_equations
-- name    : EinsteinFieldEquationsD.trace_of_field_equations
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:14:11.234323+00:00
-- url     : https://prove2.me/theorems/c879dacd-f665-4cd0-b2b4-fa4b16437931
-- title:
--   Trace of the Einstein field equations
-- statement:
--   Let $g$ be a smooth, symmetric, nondegenerate metric on an open set $U\subseteq\mathbb{R}^D$ and suppose the field equations $G_{\mu\nu}+\Lambda g_{\mu\nu}=\kappa T_{\mu\nu}$ hold on $U$. Then, taking the trace with respect to the metric,
--   $$R-\frac D2R+D\Lambda=\kappa T\qquad\text{on }U,$$
--   where $R$ is the scalar curvature and $T=g^{\mu\nu}T_{\mu\nu}$.
-- source:
--   Wikipedia, "Einstein field equations", revision oldid=1374672993, https://en.wikipedia.org/w/index.php?title=Einstein_field_equations&oldid=1374672993; section 'Equivalent formulations', first display

import Mathlib
import Definitions.Def_EinsteinFieldEquationsD_Defs

namespace EinsteinFieldEquationsD

theorem trace_of_field_equations {D : ℕ} (g T : Tensor2 D) (U : Set (Coord D)) (Λ κ : ℝ) (hg : IsMetricOn g U)
    (hEFE : EinsteinFieldEquationsOn g T Λ κ U) :
    ∀ x ∈ U, scalarCurvature g x - ((D : ℝ) / 2) * scalarCurvature g x + (D : ℝ) * Λ
      = κ * metricTrace g T x := by sorry

end EinsteinFieldEquationsD
