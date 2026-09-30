-- Prove2me | Theorems.Thm_ChitourPrescribedTime_Linear_transformed_dynamics
-- name    : ChitourPrescribedTime.Linear.transformed_dynamics
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:59:29.860748+00:00
-- url     : https://prove2.me/theorems/3013dcc2-2041-4976-bd4b-31ad7a37ba5e
-- title:
--   §3 (11) — under $y=D^{\mathbf r}_{\lambda(t)}x$, (1) becomes $y'=(a D_{\mathbf r}+J_n)y+(bu+d)e_n$
-- statement:
--   Let $T>0$ and let $a$ be an admissible weight on $[0,T]$ (continuous, nonnegative, with $\int_t^T a>0$ on $[0,T)$), and let $\lambda(t)=1/\int_t^T a$. Let $b,d,u:\mathbb R\to\mathbb R$ and $x:\mathbb R\to\mathbb R^n$. Suppose that at some instant $t\in(0,T)$ the state $x$ is differentiable and satisfies the chain of integrators (1):
--   $$\dot x(t) = J_n x(t) + \big(d(t) + b(t) u(t)\big) e_n .$$
--   Then $y(\tau) = D^{\mathbf r}_{\lambda(\tau)} x(\tau)$ is differentiable at $t$ and
--   $$\dot y(t) = \lambda(t)\Big( \big(a(t) D_{\mathbf r} + J_n\big) y(t) + \big(b(t)u(t) + d(t)\big) e_n \Big).$$
--
--   Since $ds/dt = \lambda(t)$, this is equation (11) of the paper, $y' = (a D_{\mathbf r} + J_n) y + (b u + d) e_n$, where $y'$ is the derivative with respect to the new time $s$. It reduces the prescribed-time problem for (1) to a stabilization problem on $[0,\infty)$ for a system with bounded time-varying coefficient $a$.
--
--   **Formalization Note** The identity is stated pointwise in the original time $t$, as $\dot y = \lambda\, y'$ (equation (8) of the paper), so that the inverse of the time change $s$ is not needed. The standing assumption $n\ge 1$ is not needed for this identity and is omitted.
-- source:
--   Chitour, Ushirobira, Bouhemou, Stabilization for a Perturbed Chain of Integrators in Prescribed Time, SIAM J. Control Optim. 58 (2020), pp. 1026–1027, §3, eqs. (7)–(11)

import Mathlib
import Definitions.Def_ChitourPrescribedTime_Linear_chain
import Definitions.Def_ChitourPrescribedTime_Linear_timeChange

namespace ChitourPrescribedTime.Linear

open Matrix

/-- §3, pp. 1026–1027, (7)–(11): if `x` satisfies (1), `ẋ = J_n x + (d + b u) e_n`, at an instant
`t ∈ (0, T)`, then `y = D^r_{λ(t)} x(t)` satisfies `ẏ = λ(t) · ((a(t) D_r + J_n) y + (b u + d) e_n)`
at `t`; since `ds/dt = λ`, this is (11), `y' = (a D_r + J_n) y + (b u + d) e_n`, written in the
original time. -/
theorem transformed_dynamics (n : ℕ) (T : ℝ) (a b d u : ℝ → ℝ) (x : ℝ → Fin n → ℝ)
    (ha : AdmissibleWeight T a) (t : ℝ) (ht : t ∈ Set.Ioo 0 T)
    (hx : HasDerivAt x (jordanBlock n *ᵥ x t + (d t + b t * u t) • eN n) t) :
    HasDerivAt (fun τ => dil n (lam T a τ) *ᵥ x τ)
      (lam T a t • ((a t • Dr n + jordanBlock n) *ᵥ (dil n (lam T a t) *ᵥ x t) +
        (b t * u t + d t) • eN n)) t := by sorry

end ChitourPrescribedTime.Linear
