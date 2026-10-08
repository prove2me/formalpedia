-- Prove2me | Theorems.Thm_BellmanDP_Variational_discrete_approximation_converges
-- name    : BellmanDP.Variational.discrete_approximation_converges
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T19:38:13.29631+00:00
-- url     : https://prove2.me/theorems/fad4829d-0aa6-4e97-b593-45e384286460
-- title:
--   Chapter IX, Theorem 2 (corrected) — $\lim_{n\to\infty} f(c,T,n)=f(c,T)$
-- statement:
--   Consider the control problem
--   $$f(c,T)=\sup_{\varphi}\int_0^T F(x,\varphi x)\,dt,\qquad \frac{dx}{dt}=G(x,\varphi x),\ x(0)=c,\qquad 0\le\varphi(t)\le 1,$$
--   over measurable controls $\varphi$, and for $n=1,2,\dots$ its discrete approximation with step $1/n$ and $N=\lfloor Tn\rfloor$ steps,
--   $$f(c,T,n)=\max_{0\le\varphi_k\le 1}\sum_{k=0}^{N}\frac{F(x_k,\varphi_kx_k)}{n},\qquad x_0=c,\quad x_{k+1}=x_k+\frac{G(x_k,\varphi_kx_k)}{n}.$$
--   Assume
--   1. $F$ and $G$ have continuous second partial derivatives;
--   2. there are constants $p,q,r$ with $px\le G(x,y)\le qx+r$ for $x>0$ and $0\le y\le x$;
--   3. $G_y$ is of one sign: $G_y>0$ for all $x>0$, $0\le y\le x$, or $G_y<0$ for all of them.
--
--   Then for all $c\ge 0$ and $T>0$ the set of continuous payoffs is nonempty and bounded above, and
--   $$\lim_{n\to\infty}f(c,T,n)=f(c,T).$$
--
--   The theorem justifies computing the value of a continuous-time control problem with state constraints by dynamic programming on a time grid, and is the convergence result that underlies the numerical method of Chapter IX.
--
--   **Formalization Note** The print defines the approximating problems with $N=[T/n]$ steps of length $1/n$; under that reading the discrete horizon $N/n$ tends to $0$ and the theorem is false (for $F\equiv 1$, $G(x,y)=y$, $T=1$: $f(c,1)=1$ but $f(c,1,n)=1/n$ for $n\ge 2$). The statement uses $N=\lfloor Tn\rfloor$. Assumptions (11) are on the original $F(x,y)$, $G(x,y)$; the problem is posed through $y=\varphi x$. "Max" over continuous controls is a supremum, and the statement asserts that it is taken over a nonempty set bounded above. Trajectories solve the integral equation, so measurable controls are allowed.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter IX, Theorem 2, p. 262; setup § 12, Eqs. (12.1)-(12.9), pp. 260-261

import Mathlib
import Definitions.Def_BellmanDP_Variational_Approximation

namespace BellmanDP.Variational

open Filter Topology

/-- Bellman, *Dynamic Programming*, Ch. IX, Theorem 2, p. 262 (corrected: the approximating
problems (12.5)–(12.7) use `N = ⌊T n⌋` steps of size `1 / n`; the print has `N = [T/n]`).
Under the assumptions (11) on `F (x, y)`, `G (x, y)`, for all `c ≥ 0`, `T > 0`, the set of values
`∫_0^T F (x, φ x) dt` of the continuous problem is nonempty and bounded above (so `f (c, T)` is its
supremum), and `lim_{n → ∞} f (c, T, n) = f (c, T)`. -/
theorem discrete_approximation_converges (F G : ℝ → ℝ → ℝ) (hFG : Assumptions11 F G)
    (c T : ℝ) (hc : 0 ≤ c) (hT : 0 < T) :
    (contPayoffs (phiForm F) (phiForm G) c T).Nonempty ∧
      BddAbove (contPayoffs (phiForm F) (phiForm G) c T) ∧
      Tendsto (fun n : ℕ => discreteValue (phiForm F) (phiForm G) c T n) atTop
        (𝓝 (contValue (phiForm F) (phiForm G) c T)) := by sorry

end BellmanDP.Variational
