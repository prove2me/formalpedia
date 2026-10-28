-- Prove2me | Theorems.Thm_FeynmanKac_discounted_reward_martingale_clamped
-- name    : FeynmanKac.discounted_reward_martingale_clamped
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T15:36:58.859619+00:00
-- url     : https://prove2.me/theorems/2b925be0-5560-473e-b698-cee7b34ebd0a
-- title:
--   Discounted reward of a PDE solution is a true martingale for the clamped filtration
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space carrying a bounded clock-augmented diffusion model $m$ in the sense of the Feynman–Kac bundle: an initial time $t\ge0$, a terminal time $T\ge t$, a one-dimensional Brownian motion with a Brownian filtration $(\mathcal F_r)_{r\in\mathbb R}$ indexed by elapsed time, a continuous adapted state path $s\mapsto X_s$ that solves the augmented stochastic differential equation of $m$ with bounded continuous drift and volatility, a bounded continuous potential $V\ge0$, and a bounded continuous running source $f$. For a function $u:\mathbb R\times\mathbb R\to\mathbb R$ the discounted reward of $u$ at absolute time $s$ is
--
--   $$
--   Y_s=\exp\Big(-\int_t^s V(X_q,q)\,dq\Big)\,u(X_s,s)+\int_t^s \exp\Big(-\int_t^q V(X_v,v)\,dv\Big) f(X_q,q)\,dq .
--   $$
--
--   Assume that
--
--   1. $u$ is a classical solution of the backward Feynman–Kac equation of $m$ on $[t,T]$: it is bounded on the horizon, satisfies the terminal condition, and $u_t+\mu u_x+\tfrac12\sigma^2u_{xx}-Vu+f=0$ there;
--   2. the discounted spatial gradient $D_{t,s}\,\sigma(X_s,s)\,u_x(X_s,s)$ along the path is square integrable in the sense of the bundle;
--   3. the discounted gradient integrand is admissible: jointly measurable, progressively measurable for $(\mathcal F_r)$, and of finite quadratic energy on every bounded horizon.
--
--   Then the stopped process
--
--   $$
--   r\longmapsto Y_{\,t+\min(\max(r,0),\,T-t)},\qquad r\in\mathbb R,
--   $$
--
--   is a martingale with respect to the clamped filtration $\mathcal G_r=\mathcal F_{\max(r,0)}$: it is adapted to $(\mathcal G_r)_{r\in\mathbb R}$, integrable at every index, and $E[\,Y_{\cdot}(r')\mid\mathcal G_r\,]=Y_{\cdot}(r)$ almost surely whenever $r\le r'$. For $r\ge0$ the clamped filtration is the model's own filtration, so this is the true martingale property of the discounted reward on the elapsed-time interval $[0,T-t]$, constant before time $0$ and stopped at the terminal horizon.
--
--   This theorem is the corrected form of milestone FK-07 of the Feynman–Kac mission. It replaces the earlier statement `FeynmanKac.discounted_reward_martingale`, which used the model's own filtration at every real index; for negative elapsed times that statement required $u(X_t,t)$ to be measurable for sigma algebras that the diffusion interface does not control, so it could fail for models whose path at elapsed time $0$ differs from the start on a null set. The clamped filtration is the only change.
--
--   **Formalization Note** The clamped filtration is built inline as a Mathlib `Filtration` with index $\max(r,0)$, with monotonicity and the bound by the ambient sigma algebra discharged in the statement. All other objects are exactly those of the bundle: `BoundedDiffusionModel`, `IsClassicalPDESolution`, `SquareIntegrableDiscountedGradient`, `AdmissibleDiscountedGradient` and `discountedReward`.
-- source:
--   Wikipedia Feynman–Kac formula https://en.wikipedia.org/wiki/Feynman%E2%80%93Kac_formula; James Nolen, Stanford notes Section 4.1 https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf. Corrected restatement of FeynmanKac.discounted_reward_martingale (milestone FK-07) with the filtration clamped at elapsed time 0.

import Definitions.Def_FeynmanKac_AdmissibleDiscountedGradient
import Definitions.Def_FeynmanKac_ModelReward
import Definitions.Def_FeynmanKac_ClassicalSolutionConditions
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

theorem FeynmanKac.discounted_reward_martingale_clamped
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P)
    (u : ℝ → ℝ → ℝ)
    (hu : m.IsClassicalPDESolution u)
    (hgrad : m.SquareIntegrableDiscountedGradient u)
    (hdisc : m.AdmissibleDiscountedGradient u) :
    MeasureTheory.Martingale
      (fun r ω => m.discountedReward u
        (m.initialTime + min (max r 0) (m.terminalTime - m.initialTime)) ω)
      ⟨fun r => m.filtration (max r 0),
        fun _ _ h => m.filtration.mono (max_le_max h (le_refl (0 : ℝ))),
        fun r => m.filtration.le (max r 0)⟩ P := by
  sorry
