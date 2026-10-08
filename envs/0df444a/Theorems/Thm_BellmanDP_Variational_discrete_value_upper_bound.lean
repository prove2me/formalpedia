-- Prove2me | Theorems.Thm_BellmanDP_Variational_discrete_value_upper_bound
-- name    : BellmanDP.Variational.discrete_value_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T19:37:48.343363+00:00
-- url     : https://prove2.me/theorems/f5b10ce7-f417-4bdf-9256-d2aa3313e69a
-- title:
--   Chapter IX, § 12, Eq. (12.14) — $f(c,T,n)\le f(c,T)+B'/n$
-- statement:
--   Let $F(x,y)$ and $G(x,y)$ satisfy the assumptions (11) of Chapter IX, Theorem 2, let $c>0$ and $T>0$, and let $f(c,T)$ and $f(c,T,n)$ be the values of the continuous problem and of the discrete problem with step $1/n$. Then there is a constant $B'$ such that
--   $$f(c,T,n)\le f(c,T)+\frac{B'}{n},\qquad n=1,2,\dots$$
--
--   This is the one-sided bound that gives $\limsup_{n\to\infty}f(c,T,n)\le f(c,T)$, Bellman's (12.18).
--
--   **Formalization Note** $f(c,T)$ is the supremum of the continuous payoffs and $f(c,T,n)$ the maximum of the discrete payoffs over $\varphi_0,\dots,\varphi_N\in[0,1]$, $N=\lfloor Tn\rfloor$ (corrected from the printed $[T/n]$).
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter IX, § 12, proof of Theorem 2, Eq. (12.14), p. 262

import Mathlib
import Definitions.Def_BellmanDP_Variational_Approximation

namespace BellmanDP.Variational

/-- Bellman, *Dynamic Programming*, Ch. IX, § 12, proof of Theorem 2, Eq. (12.14), p. 262: under the
assumptions (11), for `c > 0` and `T > 0` there is a constant `B′` with
`f (c, T, n) ≤ f (c, T) + B′ / n` for all `n = 1, 2, …`. -/
theorem discrete_value_upper_bound (F G : ℝ → ℝ → ℝ) (hFG : Assumptions11 F G)
    (c T : ℝ) (hc : 0 < c) (hT : 0 < T) :
    ∃ B : ℝ, ∀ n : ℕ, 0 < n →
      discreteValue (phiForm F) (phiForm G) c T n ≤ contValue (phiForm F) (phiForm G) c T + B / n := by sorry

end BellmanDP.Variational
