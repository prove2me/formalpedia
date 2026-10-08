-- Prove2me | Theorems.Thm_AhlforsComplexAnalysis_Polygon_exists_polyIn_of_isConnected
-- name    : AhlforsComplexAnalysis.Polygon.exists_polyIn_of_isConnected
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T12:35:55.94165+00:00
-- url     : https://prove2.me/theorems/b57e1597-75d9-45b8-ba93-6b3fca42999b
-- title:
--   An open connected set is polygonally connected
-- statement:
--   A *polygon* is a finite list of vertices $\ell=[v_0,v_1,\dots,v_n]$ in $\mathbb C$, traversed along the
--   segments $[v_0,v_1],\dots,[v_{n-1},v_n]$; it is *closed* if $v_0=v_n$. For $g:\mathbb C\to\mathbb C$ the integral along
--   $\ell$ is the sum of the segment integrals,
--
--   $$\int_\ell g\,dz=\sum_{k<n}\int_0^1 g\bigl(v_k+t(v_{k+1}-v_k)\bigr)\,(v_{k+1}-v_k)\,dt .$$
--
--   Integrals are interval integrals in the sense of Lean, which are $0$ for non-integrable integrands; every statement below holds under this convention, and for continuous $g$ the integral is the usual line integral.
--
--   Let $\Omega\subseteq\mathbb C$ be open and connected and let $a,b\in\Omega$. Then there is a polygon from $a$ to $b$ all of whose segments lie in $\Omega$:
--
--   $$\exists\,\ell=[a=v_0,v_1,\dots,v_n=b]\quad\text{with}\quad [v_k,v_{k+1}]\subseteq\Omega\ \ (0\le k<n).$$
--
--   This is the form of connectedness used to define a primitive of an analytic function by integrating along polygonal paths.
--
--   **Formalization Note.** `PolyIn Ω l` says every segment of `l` lies in `Ω`; the endpoints are expressed by `l.head? = some a` and `l.getLast? = some b`.
-- source:
--   L. V. Ahlfors, Complex Analysis, 3rd ed., McGraw-Hill, 1979, Ch. 3 section 1.3 (connectedness; an open set is connected iff any two points can be joined by a polygonal arc)

import Mathlib
import Definitions.Def_AhlforsComplexAnalysis_Polygon

open Set Complex Topology Filter

namespace AhlforsComplexAnalysis.Polygon

theorem exists_polyIn_of_isConnected {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    {a b : ℂ} (ha : a ∈ Ω) (hb : b ∈ Ω) :
    ∃ l : List ℂ, PolyIn Ω l ∧ l.head? = some a ∧ l.getLast? = some b := by sorry

end AhlforsComplexAnalysis.Polygon
