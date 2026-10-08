-- Prove2me | Theorems.Thm_AhlforsComplexAnalysis_Polygon_windInt_locallyConstant
-- name    : AhlforsComplexAnalysis.Polygon.windInt_locallyConstant
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T12:35:50.929658+00:00
-- url     : https://prove2.me/theorems/2a58eb14-5d8c-4578-a109-a3ea4be8b93b
-- title:
--   The winding function of a closed polygon is locally constant
-- statement:
--   A *polygon* is a finite list of vertices $\ell=[v_0,v_1,\dots,v_n]$ in $\mathbb C$, traversed along the
--   segments $[v_0,v_1],\dots,[v_{n-1},v_n]$; it is *closed* if $v_0=v_n$. For $g:\mathbb C\to\mathbb C$ the integral along
--   $\ell$ is the sum of the segment integrals,
--
--   $$\int_\ell g\,dz=\sum_{k<n}\int_0^1 g\bigl(v_k+t(v_{k+1}-v_k)\bigr)\,(v_{k+1}-v_k)\,dt .$$
--
--   Integrals are interval integrals in the sense of Lean, which are $0$ for non-integrable integrands; every statement below holds under this convention, and for continuous $g$ the integral is the usual line integral.
--
--   For a closed polygon $\ell$ and a point $a$ not on $\ell$, put
--
--   $$n(\ell,a)=\int_\ell\frac{dz}{z-a},$$
--
--   which is $2\pi i$ times the winding number of $\ell$ about $a$. Then $n(\ell,\cdot)$ is locally constant on the complement of $\ell$: every $a\notin\ell$ has a neighbourhood $V$ with
--
--   $$n(\ell,b)=n(\ell,a)\qquad\text{for all } b\in V .$$
--
--   This is the first step in showing that the winding function vanishes on the unbounded part of the complement of a closed polygon, which the general Cauchy theorem needs.
--
--   **Formalization Note.** The quantity is kept complex valued (`windInt`); integrality of the winding number is neither used nor proved. `a ∉ polyTrace l` says $a$ is not on the polygon; at points of the polygon the value of `windInt` is not meaningful and no statement here uses it.
-- source:
--   L. V. Ahlfors, Complex Analysis, 3rd ed., McGraw-Hill, 1979, Ch. 4 section 2 (index of a point with respect to a closed curve); polygonal version

import Mathlib
import Definitions.Def_AhlforsComplexAnalysis_Polygon

open Set Complex Topology Filter

namespace AhlforsComplexAnalysis.Polygon

theorem windInt_locallyConstant {l : List ℂ} (hl : IsClosedPoly l) {a : ℂ}
    (ha : a ∉ polyTrace l) : ∀ᶠ b in 𝓝 a, windInt l b = windInt l a := by sorry

end AhlforsComplexAnalysis.Polygon
