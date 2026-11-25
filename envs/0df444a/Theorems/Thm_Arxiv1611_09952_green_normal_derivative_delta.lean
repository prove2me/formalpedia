-- Prove2me | Theorems.Thm_Arxiv1611_09952_green_normal_derivative_delta
-- name    : Arxiv1611_09952.green_normal_derivative_delta
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T23:57:12.177056+00:00
-- url     : https://prove2.me/theorems/2e751c12-ce49-4009-863c-2410c0ee7d28
-- title:
--   Lemma 5: the normal derivative of the Green's function tends to the delta function on $S_2$
-- statement:
--   Let $k>0$, let $D_2$ be an obstacle with boundary $S_2$, $G_2$ the Dirichlet Green's function of $D_2'$ and $N$ the unit normal to $S_2$ pointing out of $D_2$. Let $G_{2N}(x,s)$ be the normal derivative of $G_2(x,\cdot)$ at $s\in S_2$. Then $G_{2N}(x,\cdot)\to\delta(\cdot-t)$ on $S_2$ as $x\to t\in S_2$ along any straight line non-tangential to $S_2$: for every $f\in C(S_2)$, every $t\in S_2$ and every direction $d$ with $d\cdot N(t)>0$,
--
--   $$\lim_{r\to0^+}\int_{S_2}G_{2N}(t+rd,s)\,f(s)\,ds=f(t).$$
--
--   **Formalization Note** The delta-function limit (21) is stated in the weak sense, against continuous $f$, which is what the proof establishes. A non-tangential line through $t$ meets $D_2'$ near $t$ on the side where $d\cdot N(t)>0$, which is where $G_2$ is defined.
-- source:
--   A. G. Ramm, Inverse obstacle scattering with non-over-determined data, arXiv:1611.09952v2 (2017), claim c008; Section 2, Lemma 5, eq. (21), PDF p. 7 (proof eq. (22))

import Mathlib
import Definitions.Def_Arxiv1611_09952_Basic

open MeasureTheory Filter Topology Asymptotics

namespace Arxiv1611_09952

theorem green_normal_derivative_delta (k : ℝ) (hk : 0 < k) (D₂ : Set E3) (hD₂ : IsObstacle D₂)
    (G₂ : E3 → E3 → ℂ) (hG₂ : IsDirichletGreen D₂ k G₂)
    (f : E3 → ℂ) (hf : ContinuousOn f (frontier D₂)) (t : E3) (ht : t ∈ frontier D₂)
    (d : E3) (hd : 0 < inner ℝ d (outerNormal D₂ t)) :
    Tendsto (fun r : ℝ => ∫ s, normalDeriv D₂ (fun y => G₂ (t + r • d) y) s * f s
        ∂(surfaceMeasure (frontier D₂))) (𝓝[>] 0) (𝓝 (f t)) := by sorry

end Arxiv1611_09952
