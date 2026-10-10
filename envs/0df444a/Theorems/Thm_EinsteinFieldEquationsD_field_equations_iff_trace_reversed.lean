-- Prove2me | Theorems.Thm_EinsteinFieldEquationsD_field_equations_iff_trace_reversed
-- name    : EinsteinFieldEquationsD.field_equations_iff_trace_reversed
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:14:38.320906+00:00
-- url     : https://prove2.me/theorems/5372ef3d-dbfe-4f82-8511-59da1fa5bf05
-- title:
--   Trace-reversed form of the Einstein field equations
-- statement:
--   Let $D\neq2$, let $g$ be a smooth, symmetric, nondegenerate metric on an open set $U\subseteq\mathbb{R}^D$ and $x\in U$. Then at $x$ the Einstein field equations are equivalent to their trace-reversed form:
--   $$G_{\mu\nu}+\Lambda g_{\mu\nu}=\kappa T_{\mu\nu}\ \ \forall\mu,\nu\iff R_{\mu\nu}-\frac2{D-2}\Lambda g_{\mu\nu}=\kappa\Big(T_{\mu\nu}-\frac1{D-2}Tg_{\mu\nu}\Big)\ \ \forall\mu,\nu,$$
--   with $T=g^{\mu\nu}T_{\mu\nu}$. (For $D=4$: $R_{\mu\nu}-\Lambda g_{\mu\nu}=\kappa(T_{\mu\nu}-\tfrac12Tg_{\mu\nu})$.)
-- source:
--   Wikipedia, "Einstein field equations", revision oldid=1374672993, https://en.wikipedia.org/w/index.php?title=Einstein_field_equations&oldid=1374672993; section 'Equivalent formulations', second and third displays

import Mathlib
import Definitions.Def_EinsteinFieldEquationsD_Defs

namespace EinsteinFieldEquationsD

theorem field_equations_iff_trace_reversed {D : ℕ} (hD : D ≠ 2) (g T : Tensor2 D) (U : Set (Coord D)) (Λ κ : ℝ)
    (hg : IsMetricOn g U) (x : Coord D) (hx : x ∈ U) :
    (∀ a b : Fin D, einsteinTensor g x a b + Λ * g x a b = κ * T x a b) ↔
      (∀ a b : Fin D, ricci g x a b - (2 / ((D : ℝ) - 2)) * Λ * g x a b
        = κ * (T x a b - (1 / ((D : ℝ) - 2)) * metricTrace g T x * g x a b)) := by sorry

end EinsteinFieldEquationsD
