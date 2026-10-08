-- Prove2me | Theorems.Thm_AdamDyn_ConstStep_theorem_4_3
-- name    : AdamDyn.ConstStep.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:15:38.287979+00:00
-- url     : https://prove2.me/theorems/1b220062-088b-4b6f-9f57-e72390e3b5a5
-- title:
--   Theorem 4.3 — the interpolated constant-step Adam process converges in probability to the ODE solution as $\gamma\downarrow0$
-- statement:
--   Let $f:\mathbb R^d\times\Xi\to\mathbb R$ satisfy Assumption 2.2, with $F(x)=\mathbb E f(x,\xi)$ coercive (Assumption 2.3) and $S(x)=\mathbb E\nabla f(x,\xi)^{\odot2}>0$ coordinatewise for every $x$ (Assumption 2.4). Let $\bar\alpha,\bar\beta$ satisfy Assumption 2.5 with limits $a,b$, let the samples $(\xi_n)_{n\ge1}$ be iid with the law of $\xi$ (Assumption 4.1), and let Assumption 4.2 ii) hold with $p=2$. Let $\varepsilon>0$ and $x_0\in\mathbb R^d$.
--
--   For every $\gamma>0$ let $(z^\gamma_n)_{n\in\mathbb N}$ be the constant-step Adam iterates $z^\gamma_n = T_{\gamma,\bar\alpha(\gamma),\bar\beta(\gamma)}(n,z^\gamma_{n-1},\xi_n)$ with $z^\gamma_0=(x_0,0,0)$, and let $\mathsf z^\gamma$ be their piecewise linear interpolation (2.3) on the time grid $\gamma\mathbb N$. Let $z$ be the global solution of the non-autonomous ODE $\dot z(t)=h(t,z(t))$ with $z(0)=(x_0,0,0)$. Then
--
--   $$
--   \forall T>0,\ \forall\delta>0,\qquad \lim_{\gamma\downarrow0}\ \mathbb P\Big(\sup_{t\in[0,T]}\big\|\mathsf z^\gamma(t)-z(t)\big\| > \delta\Big) = 0 .
--   $$
--
--   In words, as the step size tends to zero (with $\bar\alpha(\gamma),\bar\beta(\gamma)\to1$ at rates $a\gamma$, $b\gamma$), the constant-step Adam trajectory shadows the continuous-time Adam ODE on every bounded time window, in probability.
--
--   **Formalization Note** The theorem is stated for every global solution $z$; there is exactly one (Proposition 7.12, Theorem 3.1). The event $\sup_{t\in[0,T]}\|\cdot\|>\delta$ is written as the existence of $t\in[0,T]$ with $\|\cdot\|>\delta$, the same event. $\|\cdot\|$ is the Euclidean norm of $\mathbb R^{3d}$; $\nabla f$ is a measurable-in-$\xi$ function equal to the gradient for almost every $\xi$; probabilities of events are evaluated with $\mathbb P$ as an outer measure.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, pp. 6–7, Theorem 4.3

import Mathlib
import Definitions.Def_AdamDyn_ConstStep_StochasticModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace AdamDyn.ConstStep

/-- Theorem 4.3 (pp. 6–7): under Assumptions 2.2–2.5, 4.1 and 4.2 ii) with `p = 2`, the
interpolated constant-step Adam process converges in probability, uniformly on `[0, T]`, to the
global solution of (ODE) issued from `(x0, 0, 0)` as `γ ↓ 0`. -/
theorem theorem_4_3 {d : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (gf : E d → Ξ → E d) (ξ : ℕ → Ω → Ξ)
    (αbar βbar : ℝ → ℝ) (a b ε : ℝ) (x0 : E d) (z : ℝ → Z d)
    (h22 : Assumption22 μ f gf)
    (h23 : Tendsto (objective μ f) (cocompact (E d)) atTop)
    (h24 : ∀ x i, 0 < sqGradMean μ gf x i)
    (h25 : Assumption25 αbar βbar a b)
    (h41 : Assumption41 P μ ξ)
    (h42 : Assumption42ii μ gf 2)
    (hε : 0 < ε)
    (hz : IsGlobalSolution a b ε (objective μ f) (sqGradMean μ gf) x0 z) :
    ∀ T : ℝ, 0 < T → ∀ δ : ℝ, 0 < δ →
      Tendsto (fun γ : ℝ => P {ω | ∃ t ∈ Set.Icc 0 T,
          δ < zNorm (interp γ (adamIter gf αbar βbar ε γ x0 (fun n => ξ n ω)) t - z t)})
        (𝓝[>] 0) (𝓝 0) := by sorry

end AdamDyn.ConstStep
