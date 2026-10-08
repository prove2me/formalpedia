-- Prove2me | Theorems.Thm_AdaGrad_Full_eq_16
-- name    : AdaGrad.Full.eq_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:44:59.153183+00:00
-- url     : https://prove2.me/theorems/7ebaa03b-9de1-446b-afae-64e8d518c233
-- title:
--   Inequality (16) — telescoping the trace increments against max_{t≤T}‖x*−x_t‖₂²
-- statement:
--   Let $g_1,g_2,\dots$ and $x_1,x_2,\dots$ be arbitrary sequences in $\mathbb R^d$, $x^*\in\mathbb R^d$, $T\ge1$, and $G_t=\sum_{\tau\le t}g_\tau g_\tau^\top$. Then
--   $$\sum_{t=1}^{T-1}\|x^*-x_{t+1}\|_2^2\Big(\operatorname{tr}(G_{t+1}^{1/2})-\operatorname{tr}(G_t^{1/2})\Big)\le\max_{1\le t\le T}\|x^*-x_t\|_2^2\operatorname{tr}(G_T^{1/2})-\|x^*-x_1\|_2^2\operatorname{tr}(G_1^{1/2}).$$
--
--   Together with the previous display it bounds the divergence terms of Proposition 3 for full-matrix ADAGRAD.
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), p. 2134, (16)

import Mathlib
import Definitions.Def_AdaGrad_Full_Algorithm2
open scoped MatrixOrder InnerProductSpace

namespace AdaGrad.Full

/-- Inequality (16) (p. 2134):
`∑_{t=1}^{T−1} ‖x* − x_{t+1}‖₂² (tr G_{t+1}^{1/2} − tr G_t^{1/2})
  ≤ max_{t≤T} ‖x* − x_t‖₂² tr G_T^{1/2} − ‖x* − x_1‖₂² tr G_1^{1/2}`. -/
theorem eq_16 {d : ℕ} (g x : ℕ → EuclideanSpace ℝ (Fin d)) (xstar : EuclideanSpace ℝ (Fin d))
    (T : ℕ) (hT : 1 ≤ T) :
    ∑ t ∈ Finset.Ico 1 T, ‖xstar - x (t + 1)‖ ^ 2 * ((S g (t + 1)).trace - (S g t).trace) ≤
      (Finset.Icc 1 T).sup' (Finset.nonempty_Icc.mpr hT) (fun t => ‖xstar - x t‖ ^ 2)
          * (S g T).trace
        - ‖xstar - x 1‖ ^ 2 * (S g 1).trace := by sorry

end AdaGrad.Full
