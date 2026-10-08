-- Prove2me | Theorems.Thm_ErrBoundCplx_Cplx_theorem_14
-- name    : ErrBoundCplx.Cplx.theorem_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:22.031067+00:00
-- url     : https://prove2.me/theorems/f1d7fa9e-ab02-43a2-8a6e-96a4c0cbd870
-- title:
--   Theorem 14 — a subgradient descent sequence of a convex KL function converges strongly to a minimizer, with ‖x_k − x*‖ ≤ (b/a)φ(f(x_k)) + √(f(x_{k−1})/a)
-- statement:
--   Let $H$ be a real Hilbert space and $f : H \to (-\infty, +\infty]$ a proper, lower semicontinuous, convex function with $\operatorname{argmin} f \neq \emptyset$ and $\min f = 0$. Suppose $f$ has the KL property on $[0 < f < \bar r]$ with desingularizing function $\varphi \in \mathcal K(0, \bar r)$. Let $(x_k)_{k\in\mathbb N}$ be a subgradient descent sequence for $f$ with constants $a, b > 0$, i.e. $x_0 \in \operatorname{dom} f$ and, for each $k \ge 1$,
--   - (H1) $f(x_k) + a\|x_k - x_{k-1}\|^2 \le f(x_{k-1})$;
--   - (H2) there is $\omega_k \in \partial f(x_k)$ with $\|\omega_k\| \le b\|x_k - x_{k-1}\|$;
--
--   and suppose $f(x_0) \le r_0 < \bar r$. Then $x_k$ converges strongly to some $x^* \in \operatorname{argmin} f$, and
--   $$\|x_k - x^*\| \le \frac{b}{a}\,\varphi(f(x_k)) + \sqrt{\frac{f(x_{k-1})}{a}}, \qquad \forall k \ge 1. \tag{19}$$
--
--   The bound (19) converts a rate for the values $f(x_k)$ into a rate for the iterates; Theorem 16 combines it with the majorization $f(x_k) \le \psi(\alpha_k)$ to obtain (25).
--
--   **Formalization Note** The values $f(x_k)$ lie in $[0, r_0]$ (by (H1) the sequence $f(x_k)$ is nonincreasing) and enter $\varphi$ and the square root through `toReal`. Strong convergence is convergence in the norm topology of $H$; $x^* \in \operatorname{argmin} f$ is $f(x^*) = 0$. Completeness of $H$ is an explicit instance (`CompleteSpace H`).
-- source:
--   arXiv:1510.08234v3, Theorem 14, p. 16, (19); standing assumptions of §4, p. 14 (S = argmin f ≠ ∅, min f = 0)

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_ErrBoundCplx_Cplx_DescentSeq
open MoreauProx.Characterization NonconvexSplitting.ADMMKL
open Filter Topology

namespace ErrBoundCplx.Cplx

/-- arXiv:1510.08234v3, Theorem 14, p. 16 (with the standing assumptions of §4, p. 14:
`argmin f ≠ ∅`, `min f = 0`). A subgradient descent sequence of a proper lsc convex function
that has the KL property on `[0 < f < r̄]` with `φ ∈ K(0, r̄)`, started with `f(x₀) ≤ r₀ < r̄`,
converges strongly to a minimizer `x*`, and (19) holds for every `k ≥ 1`. -/
theorem theorem_14 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → EReal) (hf : GammaZero f) (hmin : IsMinZero f)
    (rbar : ℝ) (φ : ℝ → ℝ) (hφ : IsDesingularizer rbar φ) (hKL : KLOnBand f rbar φ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (x : ℕ → H) (hx : IsSubgradDescentSeq f a b x)
    (r0 : ℝ) (hx0 : f (x 0) ≤ (r0 : EReal)) (hr0 : r0 < rbar) :
    ∃ xstar : H, f xstar = 0 ∧ Tendsto x atTop (𝓝 xstar) ∧
      ∀ k ≥ 1, ‖x k - xstar‖
        ≤ b / a * φ (f (x k)).toReal + Real.sqrt ((f (x (k - 1))).toReal / a) := by sorry

end ErrBoundCplx.Cplx
