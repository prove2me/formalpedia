-- Prove2me | Theorems.Thm_CarrollGR_einstein_eq_trace
-- name    : CarrollGR.einstein_eq_trace
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T00:13:24.123867+00:00
-- url     : https://prove2.me/theorems/62809881-d496-4550-9ca7-edc2ee8d6d60
-- title:
--   Trace of Einstein's equation: $-R=8\pi GT$
-- statement:
--   Let $g_{\mu\nu}(x)$ have signature $(-+++)$ at a point $x$, let $G$ be a real constant (Newton's constant) and let $T_{\mu\nu}$ be any two-index field. If Einstein's equation
--
--   $$R_{\mu\nu}-\tfrac12Rg_{\mu\nu}=8\pi G\,T_{\mu\nu}$$
--
--   holds at $x$ for all $\mu,\nu$, then its trace gives
--
--   $$-R=8\pi G\,T,\qquad T=g^{\mu\nu}T_{\mu\nu}.$$
--
--   This is the first step towards the trace-reversed form (68) of Einstein's equation.
-- source:
--   S. M. Carroll, "A No-Nonsense Introduction to General Relativity" (lecture notes, 2001), uploaded PDF, p. 16, eq. (67)

import Mathlib
import Definitions.Def_CarrollGR_Defs

open scoped ContDiff

namespace CarrollGR

theorem einstein_eq_trace (g T : TensorField2) (GN : ℝ) (x : Coord) (hg : IsLorentzian (g x))
    (hE : EinsteinEq g GN T x) :
    -ricciScalar g x = 8 * Real.pi * GN * metricTrace g T x := by sorry

end CarrollGR
