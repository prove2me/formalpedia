-- Prove2me | Theorems.Thm_AhlforsComplexAnalysis_Polygon_polyInt_eq_sub_of_hasDerivAt
-- name    : AhlforsComplexAnalysis.Polygon.polyInt_eq_sub_of_hasDerivAt
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T12:35:34.673224+00:00
-- url     : https://prove2.me/theorems/d2c36062-7f63-4bb6-90f1-314a6932aa12
-- title:
--   Fundamental theorem of calculus along a polygon
-- statement:
--   A *polygon* is a finite list of vertices $\ell=[v_0,v_1,\dots,v_n]$ in $\mathbb C$, traversed along the
--   segments $[v_0,v_1],\dots,[v_{n-1},v_n]$; it is *closed* if $v_0=v_n$. For $g:\mathbb C\to\mathbb C$ the integral along
--   $\ell$ is the sum of the segment integrals,
--
--   $$\int_\ell g\,dz=\sum_{k<n}\int_0^1 g\bigl(v_k+t(v_{k+1}-v_k)\bigr)\,(v_{k+1}-v_k)\,dt .$$
--
--   Integrals are interval integrals in the sense of Lean, which are $0$ for non-integrable integrands; every statement below holds under this convention, and for continuous $g$ the integral is the usual line integral.
--
--   Let $U\subseteq\mathbb C$ be open and let $G,g:\mathbb C\to\mathbb C$ satisfy $G'(z)=g(z)$ for every $z\in U$, with $g$ continuous on $U$. If the polygon $\ell=[v_0,\dots,v_n]$ lies in $U$ (every segment is contained in $U$), then
--
--   $$\int_\ell g\,dz=G(v_n)-G(v_0).$$
--
--   In particular the integral of a derivative around a closed polygon vanishes.
--
--   **Formalization Note.** `PolyIn U l` says that every segment of `l` is contained in `U`; `l.getLast hne` and `l.head hne` are the last and first vertices.
-- source:
--   L. V. Ahlfors, Complex Analysis, 3rd ed., McGraw-Hill, 1979, Ch. 4 section 1 (the line integral of a derivative depends only on the endpoints); polygonal version

import Mathlib
import Definitions.Def_AhlforsComplexAnalysis_Polygon

open Set Complex Topology Filter

namespace AhlforsComplexAnalysis.Polygon

theorem polyInt_eq_sub_of_hasDerivAt {U : Set ℂ} (hU : IsOpen U) {G g : ℂ → ℂ}
    (hG : ∀ z ∈ U, HasDerivAt G (g z) z) (hg : ContinuousOn g U) {l : List ℂ}
    (hl : PolyIn U l) (hne : l ≠ []) :
    polyInt g l = G (l.getLast hne) - G (l.head hne) := by sorry

end AhlforsComplexAnalysis.Polygon
