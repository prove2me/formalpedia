-- Prove2me | Theorems.Thm_AhlforsComplexAnalysis_Polygon_windInt_eq_zero_of_connected_compl
-- name    : AhlforsComplexAnalysis.Polygon.windInt_eq_zero_of_connected_compl
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T12:35:52.272425+00:00
-- url     : https://prove2.me/theorems/a572e610-fa72-4dad-b657-29f591e5c50a
-- title:
--   Winding numbers about points outside a simply connected region vanish
-- statement:
--   A *polygon* is a finite list of vertices $\ell=[v_0,v_1,\dots,v_n]$ in $\mathbb C$, traversed along the
--   segments $[v_0,v_1],\dots,[v_{n-1},v_n]$; it is *closed* if $v_0=v_n$. For $g:\mathbb C\to\mathbb C$ the integral along
--   $\ell$ is the sum of the segment integrals,
--
--   $$\int_\ell g\,dz=\sum_{k<n}\int_0^1 g\bigl(v_k+t(v_{k+1}-v_k)\bigr)\,(v_{k+1}-v_k)\,dt .$$
--
--   Integrals are interval integrals in the sense of Lean, which are $0$ for non-integrable integrands; every statement below holds under this convention, and for continuous $g$ the integral is the usual line integral.
--
--   Let $\Omega\subseteq\mathbb C$ be an open set whose complement in the extended plane $\mathbb C\cup\{\infty\}$ is connected (for connected $\Omega$ this is Ahlfors' definition of a simply connected region). Let $\ell$ be a closed polygon lying in $\Omega$ and let $a\in\mathbb C\setminus\Omega$. Then
--
--   $$\int_\ell\frac{dz}{z-a}=0 ,$$
--
--   that is, the winding number of $\ell$ about every point outside $\Omega$ is zero.
--
--   This is the topological input that links Ahlfors' definition of simple connectivity to the general Cauchy theorem.
--
--   **Formalization Note.** The extended plane is `OnePoint ℂ`, and the complement of the image of `Ω` in it is required to be connected (`IsConnected`).
-- source:
--   Polygonal version of: L. V. Ahlfors, Complex Analysis, 3rd ed., McGraw-Hill, 1979, Ch. 4 section 4 (simply connected regions and the vanishing of the index outside the region); also Rudin, Real and Complex Analysis, 3rd ed., Ch. 13 (equivalent descriptions of simply connected plane regions)

import Mathlib
import Definitions.Def_AhlforsComplexAnalysis_Polygon

open Set Complex Topology Filter

namespace AhlforsComplexAnalysis.Polygon

theorem windInt_eq_zero_of_connected_compl {Ω : Set ℂ} (hΩo : IsOpen Ω)
    (hc : IsConnected ((((↑) : ℂ → OnePoint ℂ) '' Ω)ᶜ))
    {l : List ℂ} (hl : IsClosedPoly l) (hlΩ : PolyIn Ω l) {a : ℂ} (ha : a ∉ Ω) :
    windInt l a = 0 := by sorry

end AhlforsComplexAnalysis.Polygon
