-- Prove2me | Theorems.Thm_AhlforsComplexAnalysis_Polygon_polyInt_reverse
-- name    : AhlforsComplexAnalysis.Polygon.polyInt_reverse
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T12:35:26.864156+00:00
-- url     : https://prove2.me/theorems/9fca6157-d054-4e2c-8582-7a4b60baa366
-- title:
--   Reversing a polygon negates its integral
-- statement:
--   A *polygon* is a finite list of vertices $\ell=[v_0,v_1,\dots,v_n]$ in $\mathbb C$, traversed along the
--   segments $[v_0,v_1],\dots,[v_{n-1},v_n]$; it is *closed* if $v_0=v_n$. For $g:\mathbb C\to\mathbb C$ the integral along
--   $\ell$ is the sum of the segment integrals,
--
--   $$\int_\ell g\,dz=\sum_{k<n}\int_0^1 g\bigl(v_k+t(v_{k+1}-v_k)\bigr)\,(v_{k+1}-v_k)\,dt .$$
--
--   Integrals are interval integrals in the sense of Lean, which are $0$ for non-integrable integrands; every statement below holds under this convention, and for continuous $g$ the integral is the usual line integral.
--
--   Let $\bar\ell=[v_n,\dots,v_0]$ be the polygon $\ell=[v_0,\dots,v_n]$ traversed backwards. Then for every $g:\mathbb C\to\mathbb C$
--
--   $$\int_{\bar\ell}g\,dz=-\int_\ell g\,dz .$$
--
--   Together with additivity under concatenation this allows two polygons with the same endpoints to be combined into a closed polygon.
--
--   **Formalization Note.** `l.reverse` is the reversed vertex list; no integrability hypothesis is needed.
-- source:
--   L. V. Ahlfors, Complex Analysis, 3rd ed., McGraw-Hill, 1979, Ch. 4 section 1 (line integrals and their dependence on the arc); polygonal version

import Mathlib
import Definitions.Def_AhlforsComplexAnalysis_Polygon

open Set Complex Topology Filter

namespace AhlforsComplexAnalysis.Polygon

theorem polyInt_reverse (g : ℂ → ℂ) (l : List ℂ) : polyInt g l.reverse = - polyInt g l := by sorry

end AhlforsComplexAnalysis.Polygon
