-- Prove2me | Theorems.Thm_CarrollGR_einstein_eq_iff_trace_reversed
-- name    : CarrollGR.einstein_eq_iff_trace_reversed
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T00:13:44.374704+00:00
-- url     : https://prove2.me/theorems/43a3df9d-f70e-4926-a6a9-b1dd4a0412b6
-- title:
--   Einstein's equation in trace-reversed form
-- statement:
--   Let $g_{\mu\nu}(x)$ have signature $(-+++)$ at a point $x$, let $G$ be a real constant and $T_{\mu\nu}$ any two-index field, with trace $T=g^{\mu\nu}T_{\mu\nu}$. Then Einstein's equation holds at $x$ if and only if
--
--   $$R_{\mu\nu}=8\pi G\left(T_{\mu\nu}-\tfrac12T\,g_{\mu\nu}\right)\qquad\text{for all }\mu,\nu .$$
--
--   The trace-reversed form is the convenient one for vacuum problems, where it reduces to $R_{\mu\nu}=0$.
--
--   **Formalization Note** Carroll derives (68) from (57); the equivalence (both directions) is stated here, which is what "we can rewrite Einstein's equations as" asserts.
-- source:
--   S. M. Carroll, "A No-Nonsense Introduction to General Relativity" (lecture notes, 2001), uploaded PDF, p. 16, eq. (68)

import Mathlib
import Definitions.Def_CarrollGR_Defs

open scoped ContDiff

namespace CarrollGR

theorem einstein_eq_iff_trace_reversed (g T : TensorField2) (GN : ℝ) (x : Coord)
    (hg : IsLorentzian (g x)) :
    EinsteinEq g GN T x ↔
      ∀ μ ν : Fin 4, ricci g μ ν x
        = 8 * Real.pi * GN * (T x μ ν - (1 / 2 : ℝ) * metricTrace g T x * g x μ ν) := by sorry

end CarrollGR
