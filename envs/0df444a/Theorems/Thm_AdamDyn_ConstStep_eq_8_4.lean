-- Prove2me | Theorems.Thm_AdamDyn_ConstStep_eq_8_4
-- name    : AdamDyn.ConstStep.eq_8_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:58.970361+00:00
-- url     : https://prove2.me/theorems/ac5248d6-e5fe-4670-adb1-3eed47f1bfbf
-- title:
--   Eq. (8.4) — for $R\ge R_0+1$, $\mathsf z^{\gamma,R}$ converges in probability, uniformly on $[0,T]$, to the ODE solution
-- statement:
--   Assume Assumptions 2.2–2.5, 4.1 and Assumption 4.2 ii) with $p=2$, with $F$, $S$ given by (2.2), and let $\varepsilon>0$ and $x_0\in\mathbb R^d$. Let $z$ be a global solution of (ODE) with initial condition $(x_0,0,0)$ and set $R_0 := \sup_{t>0}\|\bar e(t,z(t))\|$. Then for every $R\ge R_0+1$, every $T>0$ and every $\delta>0$,
--
--   $$
--   \lim_{\gamma\to0}\ \mathbb P\Big(\sup_{t\in[0,T]}\big\|\mathsf z^{\gamma,R}(t) - z(t)\big\| > \delta\Big) = 0 ,
--   $$
--
--   where $\mathsf z^{\gamma,R}$ is the interpolated process of the Adam iterates stopped when the debiased iterate first leaves the ball of radius $R$.
--
--   It remains, to obtain Theorem 4.3, to show that the stopping is asymptotically never triggered on $[0,T]$.
--
--   **Formalization Note** "$R\ge R_0+1$" is stated as $\|\bar e(t,z(t))\|+1\le R$ for all $t>0$, which avoids a real supremum that would be junk if unbounded (Proposition 7.6 shows $R_0<\infty$). The event $\sup_{t\in[0,T]}\|\cdot\|>\delta$ is written as "some $t\in[0,T]$ has $\|\cdot\|>\delta$", which is the same event. The limit is $\gamma\downarrow0$. $\|\cdot\|$ is the Euclidean norm of $\mathbb R^{3d}$.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 23, §8.1, Eq. (8.4) (with R0 defined on p. 22)

import Mathlib
import Definitions.Def_AdamDyn_ConstStep_StochasticModel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace AdamDyn.ConstStep

/-- Eq. (8.4) (§8.1, p. 23): with `R0 := sup_{t>0} ‖ē(t, z(t))‖` for the global solution `z`,
for every `R ≥ R0 + 1`, every `T > 0` and every `δ > 0`,
`lim_{γ→0} P(sup_{t∈[0,T]} ‖𝗓^{γ,R}(t) − z(t)‖ > δ) = 0`. -/
theorem eq_8_4 {d : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
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
    ∀ R : ℝ, (∀ t : ℝ, 0 < t → zNorm (AdamDyn.ODEConv.ebar a b t (z t)) + 1 ≤ R) →
    ∀ T : ℝ, 0 < T → ∀ δ : ℝ, 0 < δ →
      Tendsto (fun γ : ℝ => P {ω | ∃ t ∈ Set.Icc 0 T,
          δ < zNorm (interp γ (truncIter gf αbar βbar ε γ R x0 (fun n => ξ n ω)) t - z t)})
        (𝓝[>] 0) (𝓝 0) := by sorry

end AdamDyn.ConstStep
