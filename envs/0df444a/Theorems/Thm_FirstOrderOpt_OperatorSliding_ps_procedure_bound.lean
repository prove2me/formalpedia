-- Prove2me | Theorems.Thm_FirstOrderOpt_OperatorSliding_ps_procedure_bound
-- name    : FirstOrderOpt.OperatorSliding.ps_procedure_bound
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T21:05:40.004856+00:00
-- url     : https://prove2.me/theorems/793be9fe-bf1f-455b-909e-c07d699ff0c4
-- title:
--   Proposition 8.1 — convergence of the prox-sliding (PS) procedure
-- statement:
--   The gradient sliding (GS) algorithm for the composite problem $\Psi^* := \min_{x\in X}
--   \{\Psi(x) := f(x)+h(x)+\chi(x)\}$ (8.1.1), where $X\subseteq E$, a real inner product space, is closed convex,
--   $\chi$ is a "relatively simple" convex function, $f$ is $L$-smooth (8.1.2), and $h$ is
--   nonsmooth convex satisfying, for some $M>0$ and $h'(y)\in\partial h(y)$,
--   $$h(x) \le h(y) + \langle h'(y), x-y\rangle + M\|x-y\|, \qquad \forall x,y\in X, \quad (8.1.3)$$
--   delegates the inner work of approximately solving its subproblem to the **prox-sliding (PS)
--   procedure**. Given an affine model $g$, a prox-center $x\in X$, a parameter $\beta>0$, and a
--   sliding length $T$, PS runs, for $t=1,\dots,T$,
--   $$u_t = \arg\min_{u\in X}\{g(u)+l_h(u_{t-1},u)+\beta V(x,u)+\beta p_tV(u_{t-1},u)+\chi(u)\},
--   \qquad \tilde u_t = (1-\theta_t)\tilde u_{t-1}+\theta_tu_t, \quad (8.1.17)\text{--}(8.1.18)$$
--   where $u_0=\tilde u_0=x$, $l_h(y;u):=h(y)+\langle h'(y),u-y\rangle$ (8.1.14), and $V$ is the
--   prox-function (Bregman-type divergence) of Sect. 3.2's distance-generating function $\nu$
--   (modulus 1, so $V(a,b)\ge\|b-a\|^2/2$). This is the problem of approximately minimizing
--   $$\Phi(u) := g(u)+h(u)+\beta V(x,u)+\chi(u), \qquad u\in X. \quad (8.1.19)$$
--
--   **Proposition 8.1.** If $\{p_t\}$ and $\{\theta_t\}$ in the PS procedure satisfy
--   $$\theta_t = \frac{P_{t-1}-P_t}{(1-P_t)P_{t-1}} \quad\text{with}\quad P_t :=
--   \begin{cases}1, & t=0\\ p_t(1+p_t)^{-1}P_{t-1}, & t\ge1,\end{cases} \quad (8.1.20)$$
--   then, for any $t\ge1$ and $u\in X$,
--   $$\beta(1-P_t)^{-1}V(u_t,u) + [\Phi(\tilde u_t)-\Phi(u)] \le P_t(1-P_t)^{-1}\Big[\beta
--   V(u_0,u) + \frac{M^2}{2\beta}\sum_{i=1}^t(p_i^2P_{i-1})^{-1}\Big]. \quad (8.1.21)$$
--
--   This is the per-inner-iteration guarantee that quantifies how close the PS procedure's pair of
--   approximate solutions $(u_t,\tilde u_t)$ comes to solving (8.1.19); the outer GS algorithm's own
--   convergence (`gs_convergence_bound`, Theorem 8.1) is built by composing this bound across
--   outer steps.
--
--   **Formalization Note.** `huThreePoint` states the three-point inequality that `u t` solving
--   (8.1.17) yields by Lemma 3.5 of Sect. 3.2 (cited, not restated — it is the standard consequence
--   of a strongly-convex-regularized Bregman-proximal minimizer, used exactly as the book's proof
--   uses it, "applying Lemma 3.5 to (8.1.17)"). `lh` is $l_h$ of (8.1.14), left as a hypothesis
--   object via `hMLip`, which is exactly (8.1.3) with $l_h$ in place of the explicit
--   subgradient formula (both are the same content the proof cites). `hVstrong` is $V(a,b)\ge
--   \|b-a\|^2/2$, the strong-convexity property of $\nu$ used inside the proof (not restated as a
--   derivation from a distance-generating function, per the book's own abstraction level for $V$
--   elsewhere in the series).
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 489, Proposition 8.1

import Mathlib

namespace FirstOrderOpt.OperatorSliding

open scoped RealInnerProductSpace

/-- Proposition 8.1 (convergence of the prox-sliding, PS, procedure). `PS(g,x,β,T)` runs
`u_t = argmin_{u∈X}{g(u)+lh(u_{t-1},u)+βV(x,u)+βp_tV(u_{t-1},u)+χ(u)}` (8.1.17) and
`ũ_t = (1-θ_t)ũ_{t-1}+θ_tu_t` (8.1.18); `Φ(u) := g(u)+h(u)+βV(x,u)+χ(u)` (8.1.19).
`huThreePoint` is the three-point inequality that `u t` solving (8.1.17) yields by Lemma 3.5
(cited, not restated). `hMLip` is (8.1.3): `h(z) ≤ lh(y,z)+M‖z-y‖`. `hVstrong` is `V ≥ ‖·‖²/2`,
the strong-convexity property of the distance-generating function `ν` (Sect. 3.2), used together
with `hMLip` inside the proof to bound `-βp_tV(u_{t-1},u_t)+M‖u_t-u_{t-1}‖`. If `{p_t},{θ_t}`
satisfy (8.1.20) (`P_0=1`, `P_t=p_t(1+p_t)^{-1}P_{t-1}`, `θ_t=(P_{t-1}-P_t)/((1-P_t)P_{t-1})`),
then for any `t≥1` and `u∈X`, (8.1.21) holds. -/
theorem ps_procedure_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (g h chi : E → ℝ) (lh : E → E → ℝ) (V : E → E → ℝ)
    (x : E) (β M : ℝ) (hβ : 0 < β) (hM : 0 < M)
    (hVnonneg : ∀ a b, 0 ≤ V a b)
    (hVstrong : ∀ a b, (1 / 2) * ‖b - a‖ ^ 2 ≤ V a b)
    (hMLip : ∀ y ∈ X, ∀ z ∈ X, h z ≤ lh y z + M * ‖z - y‖)
    (Φ : E → ℝ) (hΦ : ∀ u, Φ u = g u + h u + β * V x u + chi u)
    (p θ P : ℕ → ℝ) (hp : ∀ t, 0 < p t)
    (hP0 : P 0 = 1)
    (hPrec : ∀ t : ℕ, 1 ≤ t → P t = p t * (1 + p t)⁻¹ * P (t - 1))
    (hθ : ∀ t : ℕ, 1 ≤ t → θ t = (P (t - 1) - P t) / ((1 - P t) * P (t - 1)))
    (u ũ : ℕ → E) (hu0 : u 0 = x) (hũ0 : ũ 0 = x) (hmem : ∀ t, u t ∈ X)
    (huThreePoint : ∀ t : ℕ, 1 ≤ t → ∀ w ∈ X,
      g (u t) + lh (u (t - 1)) (u t) + β * V x (u t) + chi (u t)
          + β * p t * V (u (t - 1)) (u t) ≤
        g w + lh (u (t - 1)) w + β * V x w + chi w + β * p t * V (u (t - 1)) w
          - β * (1 + p t) * V (u t) w)
    (hũrec : ∀ t : ℕ, 1 ≤ t → ũ t = (1 - θ t) • ũ (t - 1) + θ t • u t)
    (t : ℕ) (ht : 1 ≤ t) (w : E) (hw : w ∈ X) :
    β * (1 - P t)⁻¹ * V (u t) w + (Φ (ũ t) - Φ w) ≤
      P t * (1 - P t)⁻¹ *
        (β * V x w + (M ^ 2 / (2 * β)) * ∑ i ∈ Finset.Icc 1 t, (p i ^ 2 * P (i - 1))⁻¹) := by sorry

end FirstOrderOpt.OperatorSliding
