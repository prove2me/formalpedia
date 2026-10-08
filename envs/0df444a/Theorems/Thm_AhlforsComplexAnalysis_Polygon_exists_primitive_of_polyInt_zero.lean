-- Prove2me | Theorems.Thm_AhlforsComplexAnalysis_Polygon_exists_primitive_of_polyInt_zero
-- name    : AhlforsComplexAnalysis.Polygon.exists_primitive_of_polyInt_zero
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T12:35:31.133987+00:00
-- url     : https://prove2.me/theorems/dbc0e401-2b51-4f16-b964-aa3c621410af
-- title:
--   Vanishing integrals over closed polygons give a primitive
-- statement:
--   A *polygon* is a finite list of vertices $\ell=[v_0,v_1,\dots,v_n]$ in $\mathbb C$, traversed along the
--   segments $[v_0,v_1],\dots,[v_{n-1},v_n]$; it is *closed* if $v_0=v_n$. For $g:\mathbb C\to\mathbb C$ the integral along
--   $\ell$ is the sum of the segment integrals,
--
--   $$\int_\ell g\,dz=\sum_{k<n}\int_0^1 g\bigl(v_k+t(v_{k+1}-v_k)\bigr)\,(v_{k+1}-v_k)\,dt .$$
--
--   Integrals are interval integrals in the sense of Lean, which are $0$ for non-integrable integrands; every statement below holds under this convention, and for continuous $g$ the integral is the usual line integral.
--
--   Let $\Omega\subseteq\mathbb C$ be open and connected and let $g$ be continuous on $\Omega$. Suppose that $\int_\ell g\,dz=0$ for every closed polygon $\ell$ lying in $\Omega$. Then $g$ has a primitive on $\Omega$: there is $G$ with
--
--   $$G'(z)=g(z)\qquad(z\in\Omega).$$
--
--   This is the converse of the fundamental theorem of calculus along polygons, and the step that turns Cauchy's theorem into the existence of logarithms and roots.
--
--   **Formalization Note.** `IsClosedPoly l` means that `l` is nonempty and its first and last vertices agree; `PolyIn Ω l` means every segment of `l` lies in `Ω`.
-- source:
--   L. V. Ahlfors, Complex Analysis, 3rd ed., McGraw-Hill, 1979, Ch. 4 section 1 (integrals independent of the path are integrals of derivatives); polygonal version

import Mathlib
import Definitions.Def_AhlforsComplexAnalysis_Polygon

open Set Complex Topology Filter

namespace AhlforsComplexAnalysis.Polygon

theorem exists_primitive_of_polyInt_zero {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    {g : ℂ → ℂ} (hg : ContinuousOn g Ω)
    (h0 : ∀ l : List ℂ, IsClosedPoly l → PolyIn Ω l → polyInt g l = 0) :
    ∃ G : ℂ → ℂ, ∀ z ∈ Ω, HasDerivAt G (g z) z := by sorry

end AhlforsComplexAnalysis.Polygon
