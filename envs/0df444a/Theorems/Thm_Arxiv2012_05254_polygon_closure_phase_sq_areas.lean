-- Prove2me | Theorems.Thm_Arxiv2012_05254_polygon_closure_phase_sq_areas
-- name    : Arxiv2012_05254.polygon_closure_phase_sq_areas
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T04:53:39.091536+00:00
-- url     : https://prove2.me/theorems/3814a84d-3d90-5a94-8bab-5e4963343e4e
-- title:
--   Eq. (27): the squared closure phase of an $N$-polygon in terms of elemental-triad areas
-- statement:
--   Let $N\ge3$ elements at positions $x_0,\dots,x_{N-1}$ form a closed $N$-polygon. Let $\psi_{ab}$ be NPC phase offsets with $\psi_{ba}=-\psi_{ab}$. For $q=1,\dots,N-2$, let the elemental triad $(0,q,q+1)$ be non-collinear, with closure phase $\psi_{3(q)}$, aperture area $A_{\mathcal A3(q)}$ and NPC triangle area $A_{\mathcal I3(q)}$. Then
--
--   $$\psi_N^2=16\pi^2\sum_{q=1}^{N-2}A_{\mathcal A3(q)}A_{\mathcal I3(q)}+2\sum_{q=1}^{N-3}\sum_{r=q+1}^{N-2}\psi_{3(q)}\psi_{3(r)}.$$
--
--   For $N=4$ this is eq. (26).
-- source:
--   Thyagarajan and Carilli, A Geometric View of Closure Phases in Interferometry, arXiv:2012.05254v3, Publ. Astron. Soc. Aust. 38 (2021), claim c025; Appendix 2, eqs. (25)-(27), PDF p. 17

import Mathlib
import Definitions.Def_Arxiv2012_05254_Basic

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace Arxiv2012_05254

theorem polygon_closure_phase_sq_areas {M : ℕ} (hM : 1 ≤ M) (x : Fin (M + 2) → Plane)
    (ψ : Fin (M + 2) → Fin (M + 2) → ℝ) (hψ : ∀ a b, ψ b a = -ψ a b)
    (hx : ∀ q : Fin M, AffineIndependent ℝ (x ∘ fanTriad q)) :
    closurePhase (loopPhase ψ id) ^ 2 =
      16 * Real.pi ^ 2 * ∑ q : Fin M,
          apertureArea (x ∘ fanTriad q) * imageArea (x ∘ fanTriad q) (loopPhase ψ (fanTriad q)) +
        2 * ∑ q : Fin M, ∑ r ∈ Finset.Ioi q,
          closurePhase (loopPhase ψ (fanTriad q)) * closurePhase (loopPhase ψ (fanTriad r)) := by sorry

end Arxiv2012_05254
