-- Prove2me | Theorems.Thm_ErrBoundCplx_Cplx_eq_20
-- name    : ErrBoundCplx.Cplx.eq_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:03.984311+00:00
-- url     : https://prove2.me/theorems/e6692b1e-195b-45ac-9760-bb0023396d2d
-- title:
--   (20), proof of Theorem 14 — φ(f(x_k)) − φ(f(x_{k+1})) ≥ (a/b)(2‖x_k − x_{k+1}‖ − ‖x_{k−1} − x_k‖) when f(x_k) > 0, x_k ≠ x_{k−1}
-- statement:
--   Let $H$ be a real Hilbert space and $f : H \to (-\infty, +\infty]$ proper, lower semicontinuous and convex, with $\min f = 0$ attained. Let $0 < \bar r$ and suppose $f$ has the KL property on $[0 < f < \bar r]$ with desingularizing function $\varphi \in \mathcal K(0, \bar r)$. Let $(x_k)_{k\in\mathbb N}$ be a subgradient descent sequence for $f$ with constants $a, b > 0$ (conditions (H1), (H2)) and $f(x_0) \le r_0 < \bar r$. Assume moreover that
--   $$f(x_k) > 0 \quad\text{and}\quad \|x_k - x_{k-1}\| > 0 \qquad \text{for all } k \ge 1.$$
--   Then for every $k \ge 1$,
--   $$\begin{aligned}
--   \varphi(f(x_k)) - \varphi(f(x_{k+1})) &\ge \varphi'(f(x_k))\,\big(f(x_k) - f(x_{k+1})\big)\\
--   &\ge \frac{a\|x_k - x_{k+1}\|^2}{b\|x_{k-1} - x_k\|}\\
--   &\ge \frac{a}{b}\,\frac{2\|x_k - x_{k+1}\|\,\|x_k - x_{k-1}\| - \|x_{k-1} - x_k\|^2}{\|x_k - x_{k-1}\|}\\
--   &\ge \frac{a}{b}\big(2\|x_k - x_{k+1}\| - \|x_{k-1} - x_k\|\big).
--   \end{aligned}$$
--
--   This is the key estimate of the proof of Theorem 14: summed over $k$, it bounds the length $\sum\|x_k - x_{k+1}\|$ of the sequence by values of $\varphi$, which gives strong convergence and the bound (19).
--
--   **Formalization Note** The values $f(x_j)$ are real numbers here ($0 \le f(x_j) \le f(x_0) \le r_0$) and enter through `toReal`; $\varphi'$ is `deriv φ`, evaluated only at $f(x_k) \in (0, \bar r)$. The four inequalities of the display are stated as a conjunction.
-- source:
--   arXiv:1510.08234v3, proof of Theorem 14, (20), p. 16 (the case f(x_k) > 0 and ‖x_k − x_{k−1}‖ > 0 for all k ≥ 1)

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_ErrBoundCplx_Cplx_DescentSeq
open MoreauProx.Characterization NonconvexSplitting.ADMMKL
open Filter Topology

namespace ErrBoundCplx.Cplx

/-- arXiv:1510.08234v3, proof of Theorem 14, (20), p. 16. Setting of Theorem 14 (a proper lsc
convex `f` with `min f = 0` attained, KL on `[0 < f < r̄]` with `φ ∈ K(0, r̄)`, a subgradient
descent sequence with constants `a, b > 0` and `f(x₀) ≤ r₀ < r̄`), in the case first treated in
the proof: `f(x_k) > 0` and `‖x_k − x_{k−1}‖ > 0` for all `k ≥ 1`. Writing `r_j = f(x_j)` (a real
number), for every `k ≥ 1` the four inequalities of the display (20) hold. -/
theorem eq_20 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → EReal) (hf : GammaZero f) (hmin : IsMinZero f)
    (rbar : ℝ) (φ : ℝ → ℝ) (hφ : IsDesingularizer rbar φ) (hKL : KLOnBand f rbar φ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (x : ℕ → H) (hx : IsSubgradDescentSeq f a b x)
    (r0 : ℝ) (hx0 : f (x 0) ≤ (r0 : EReal)) (hr0 : r0 < rbar)
    (hpos : ∀ j ≥ 1, 0 < f (x j) ∧ 0 < ‖x j - x (j - 1)‖) :
    ∀ k ≥ 1,
      deriv φ (f (x k)).toReal * ((f (x k)).toReal - (f (x (k + 1))).toReal)
          ≤ φ (f (x k)).toReal - φ (f (x (k + 1))).toReal ∧
        a * ‖x k - x (k + 1)‖ ^ 2 / (b * ‖x (k - 1) - x k‖)
          ≤ deriv φ (f (x k)).toReal * ((f (x k)).toReal - (f (x (k + 1))).toReal) ∧
        a / b * ((2 * ‖x k - x (k + 1)‖ * ‖x k - x (k - 1)‖ - ‖x (k - 1) - x k‖ ^ 2)
            / ‖x k - x (k - 1)‖)
          ≤ a * ‖x k - x (k + 1)‖ ^ 2 / (b * ‖x (k - 1) - x k‖) ∧
        a / b * (2 * ‖x k - x (k + 1)‖ - ‖x (k - 1) - x k‖)
          ≤ a / b * ((2 * ‖x k - x (k + 1)‖ * ‖x k - x (k - 1)‖ - ‖x (k - 1) - x k‖ ^ 2)
            / ‖x k - x (k - 1)‖) := by sorry

end ErrBoundCplx.Cplx
