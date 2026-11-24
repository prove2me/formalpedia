-- Prove2me | Theorems.Thm_Arxiv1507_03491_near_source_orders_and_image
-- name    : Arxiv1507_03491.near_source_orders_and_image
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T17:52:20.83207+00:00
-- url     : https://prove2.me/theorems/e53c2d3f-684b-49b8-8d24-907e84a44656
-- title:
--   Remark 6: orders of $G_k$ and $\partial G_k/\partial n$ on $\Gamma$ for a near source, and the image-source cancellation
-- statement:
--   Let $\operatorname{Re}k>0$ and $\operatorname{Im}k\ge0$, and consider a source at $(0,h)$. As $h\to0^+$:
--
--   1. the normal derivative of $G_k$ on $\Gamma$ is $O(1/h)$ uniformly on $\Gamma$: there are $C$ and $h_0>0$ with $\big|\partial_yG_k((x,y),(0,h))\big|_{y=0}\big|\le C/h$ for all $x\in\mathbb R$ and $0<h<h_0$;
--   2. $G_k$ on $\Gamma$ is $O(\log h)$ uniformly on $\Gamma$: there are $C$ and $h_0>0$ with $|G_k((x,0),(0,h))|\le C|\log h|$ for all $x\in\mathbb R$ and $0<h<h_0$;
--   3. an image source of the same strength at the reflected point $(0,-h)$ cancels the normal derivative on $\Gamma$: for every $h>0$ and $x\in\mathbb R$,
--
--   $$\frac{\partial}{\partial y}\Big(G_k((x,y),(0,h))+G_k((x,y),(0,-h))\Big)\Big|_{y=0}=0.$$
--
--   These facts explain the stabilization used in the numerical examples for sources very close to the interface.
--
--   **Formalization Note** "Of the order $O(\cdot)$" is read as an upper bound as $h\to0^+$, uniform over the points of $\Gamma$. The remark's statements about finite-precision cancellation and the numerical procedure are not mathematical claims and are not included.
-- source:
--   Lai, Greengard and O'Neil, A new hybrid integral representation for frequency domain scattering in layered media, arXiv:1507.03491v2 (2015), claim c017; Section 7.1, Remark 6, PDF p. 15

import Mathlib
import Definitions.Def_Arxiv1507_03491_Basic

open MeasureTheory Filter Topology Set
open scoped ContDiff NNReal

namespace Arxiv1507_03491

theorem near_source_orders_and_image (k : ℂ) (hk : 0 < k.re) (hk' : 0 ≤ k.im) :
    (∃ C h0 : ℝ, 0 < h0 ∧ ∀ h ∈ Ioo 0 h0, ∀ x : ℝ,
      ‖deriv (fun t : ℝ => greenK k x t 0 h) 0‖ ≤ C / h) ∧
    (∃ C h0 : ℝ, 0 < h0 ∧ ∀ h ∈ Ioo 0 h0, ∀ x : ℝ,
      ‖greenK k x 0 0 h‖ ≤ C * |Real.log h|) ∧
    (∀ h : ℝ, 0 < h → ∀ x : ℝ,
      deriv (fun t : ℝ => greenK k x t 0 h + greenK k x t 0 (-h)) 0 = 0) := by sorry

end Arxiv1507_03491
