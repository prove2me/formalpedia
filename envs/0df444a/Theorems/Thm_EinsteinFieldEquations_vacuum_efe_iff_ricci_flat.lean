-- Prove2me | Theorems.Thm_EinsteinFieldEquations_vacuum_efe_iff_ricci_flat
-- name    : EinsteinFieldEquations.vacuum_efe_iff_ricci_flat
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-20T23:46:21.626615+00:00
-- url     : https://prove2.me/theorems/e145ef8c-5b1b-44aa-b03a-73d1ae819483
-- title:
--   Vacuum field equations are Ricci-flatness
-- statement:
--   **Vacuum field equations.** Let $g$ be a metric whose matrix is invertible at the point $x$. Then $g$ satisfies the Einstein field equations at $x$ with vanishing cosmological constant and vanishing stress–energy tensor if and only if its Ricci tensor vanishes at $x$:
--
--   $$G_{ab}(x) = 0 \ \text{ for all } a,b \qquad\Longleftrightarrow\qquad R_{ab}(x) = 0 \ \text{ for all } a,b.$$
--
--   This is the source's statement that setting $T = 0$ in the trace-reversed field equations gives the Einstein vacuum equations $R_{\mu\nu} = 0$, whose solutions are the Ricci-flat metrics.
-- source:
--   Wikipedia, "Einstein field equations", https://en.wikipedia.org/wiki/Einstein_field_equations, section "Vacuum field equations" (Einstein vacuum equations $R_{\mu\nu} = 0$; Ricci-flat manifolds)

import Definitions.Def_efe_geometry

namespace EinsteinFieldEquations

theorem vacuum_efe_iff_ricci_flat (g : Tensor2Field) (kappa : ℝ) (x : Coord)
    (hg : IsUnit (g x).det) :
    SatisfiesEFE g 0 kappa (fun _ => 0) x ↔ ∀ a b : Fin 4, ricci g a b x = 0 := by sorry

end EinsteinFieldEquations
