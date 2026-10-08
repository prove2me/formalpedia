-- Prove2me | Theorems.Thm_AhlforsComplexAnalysis_Polygon_polyInt_append
-- name    : AhlforsComplexAnalysis.Polygon.polyInt_append
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T12:35:09.852724+00:00
-- url     : https://prove2.me/theorems/de42675b-08a1-4196-a043-1bbc6135d801
-- title:
--   Polygon integrals add under concatenation
-- statement:
--   A *polygon* is a finite list of vertices $\ell=[v_0,v_1,\dots,v_n]$ in $\mathbb C$, traversed along the
--   segments $[v_0,v_1],\dots,[v_{n-1},v_n]$; it is *closed* if $v_0=v_n$. For $g:\mathbb C\to\mathbb C$ the integral along
--   $\ell$ is the sum of the segment integrals,
--
--   $$\int_\ell g\,dz=\sum_{k<n}\int_0^1 g\bigl(v_k+t(v_{k+1}-v_k)\bigr)\,(v_{k+1}-v_k)\,dt .$$
--
--   Integrals are interval integrals in the sense of Lean, which are $0$ for non-integrable integrands; every statement below holds under this convention, and for continuous $g$ the integral is the usual line integral.
--
--   Let $\ell=[v_0,\dots,v_n]$ and $m=[w_0,\dots,w_k]$ be nonempty polygons such that the last vertex of $\ell$ is the first vertex of $m$, $v_n=w_0$. The concatenation $\ell\cdot m=[v_0,\dots,v_n,w_1,\dots,w_k]$ satisfies, for every $g:\mathbb C\to\mathbb C$,
--
--   $$\int_{\ell\cdot m}g\,dz=\int_\ell g\,dz+\int_m g\,dz .$$
--
--   This is the bookkeeping identity that lets path-independence arguments be phrased as the vanishing of integrals over closed polygons.
--
--   **Formalization Note.** The concatenation is `l ++ m.tail`, with hypotheses `l ≠ []`, `m ≠ []` and `l.getLast? = m.head?`.
-- source:
--   L. V. Ahlfors, Complex Analysis, 3rd ed., McGraw-Hill, 1979, Ch. 4 section 1 (line integrals and their dependence on the arc); polygonal version

import Mathlib
import Definitions.Def_AhlforsComplexAnalysis_Polygon

open Set Complex Topology Filter

namespace AhlforsComplexAnalysis.Polygon

theorem polyInt_append (g : ℂ → ℂ) {l m : List ℂ} (hl : l ≠ []) (hm : m ≠ [])
    (h : l.getLast? = m.head?) : polyInt g (l ++ m.tail) = polyInt g l + polyInt g m := by sorry

end AhlforsComplexAnalysis.Polygon
