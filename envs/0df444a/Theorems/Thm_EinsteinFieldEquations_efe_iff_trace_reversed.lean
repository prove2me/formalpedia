-- Prove2me | Theorems.Thm_EinsteinFieldEquations_efe_iff_trace_reversed
-- name    : EinsteinFieldEquations.efe_iff_trace_reversed
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-20T23:45:55.380618+00:00
-- url     : https://prove2.me/theorems/74993309-77e0-4904-98ae-5a614b8432a2
-- title:
--   Equivalence of the EFE with their trace-reversed form
-- statement:
--   **Trace-reversed form of the field equations.** Let $g$ be a metric whose matrix is invertible at the point $x$, let $T$ be a stress–energy tensor, and let $\Lambda, \kappa$ be real parameters. Then the Einstein field equations at $x$,
--
--   $$R_{ab} - \tfrac12 R\,g_{ab} + \Lambda\, g_{ab} \;=\; \kappa\, T_{ab},$$
--
--   hold if and only if
--
--   $$R_{ab} \;=\; \kappa\left(T_{ab} - \tfrac12\, T\, g_{ab}\right) + \Lambda\, g_{ab}, \qquad T := g^{cd}T_{cd}.$$
--
--   Taking the $g$-trace of the field equations in spacetime dimension $4$ gives $R = 4\Lambda - \kappa T$; substituting this back yields the displayed form, and reversing the trace again restores the original equations. This is the equivalence stated in the "Equivalent formulations" section of the source, specialized to dimension $4$.
-- source:
--   Wikipedia, "Einstein field equations", https://en.wikipedia.org/wiki/Einstein_field_equations, section "Equivalent formulations" (trace-reversed form; the displayed specialization to spacetime dimension 4)

import Definitions.Def_efe_geometry

namespace EinsteinFieldEquations

theorem efe_iff_trace_reversed (g T : Tensor2Field) (Lam kappa : ℝ) (x : Coord)
    (hg : IsUnit (g x).det) :
    SatisfiesEFE g Lam kappa T x ↔
      ∀ a b : Fin 4, ricci g a b x
        = kappa * (T x a b - (1 / 2 : ℝ) * metricTrace g T x * (g x) a b)
          + Lam * (g x) a b := by sorry

end EinsteinFieldEquations
