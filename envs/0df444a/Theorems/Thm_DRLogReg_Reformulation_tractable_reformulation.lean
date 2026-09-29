-- Prove2me | Theorems.Thm_DRLogReg_Reformulation_tractable_reformulation
-- name    : DRLogReg.Reformulation.tractable_reformulation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:37:08.217377+00:00
-- url     : https://prove2.me/theorems/e2d9f7de-e654-4cd7-8cc5-4f69a90bf889
-- title:
--   Theorem 1 — the distributionally robust logistic regression problem (6) equals the convex program (7)
-- statement:
--   Let $V$ be a finite-dimensional real vector space (the feature space $\mathbb R^n$) equipped with an arbitrary norm $\|\cdot\|$, with dual norm $\|\cdot\|_*$. Let $\kappa>0$ be the label weight of the metric $d((x,y),(x',y')) = \|x-x'\|+\kappa|y-y'|/2$ on $\Xi=V\times\{-1,+1\}$, let $\varepsilon\ge0$, and let $(\hat x_i,\hat y_i)_{i=1}^N$ be training samples with $N\ge1$ and empirical distribution $\hat{\mathbb P}_N$. Then
--   $$\hat J := \inf_\beta\ \sup_{\mathbb Q\in\mathbb B_\varepsilon(\hat{\mathbb P}_N)}\mathbb E^{\mathbb Q}\big[l_\beta(x,y)\big] \;=\; \left\{\begin{aligned}\inf_{\beta,\lambda,s}\quad&\lambda\varepsilon+\frac1N\sum_{i=1}^N s_i\\ \text{s.t.}\quad& l_\beta(\hat x_i,\hat y_i)\le s_i && \forall i\le N\\ & l_\beta(\hat x_i,-\hat y_i)-\lambda\kappa\le s_i && \forall i\le N\\ & \|\beta\|_*\le\lambda,\end{aligned}\right.$$
--   where $l_\beta(x,y)=\log(1+\exp(-y\langle\beta,x\rangle))$ is the logloss and $\mathbb B_\varepsilon(\hat{\mathbb P}_N)$ is the type-1 Wasserstein ball of radius $\varepsilon$ around $\hat{\mathbb P}_N$. Moreover, if $\varepsilon>0$, the infimum of program (7) is attained.
--
--   This is the first main result of the paper: the distributionally robust logistic regression problem over a Wasserstein ball, an optimization over infinitely many distributions, is equivalent to a finite-dimensional convex program.
--
--   **Correction of the printed statement.** The paper writes "min" in (7) for every $\varepsilon\ge0$. At $\varepsilon=0$ the minimum need not be attained: with $V=\mathbb R$, $N=1$, $\hat x_1=1$, $\hat y_1=+1$, the optimal value is $\inf_\beta\log(1+e^{-\beta})=0$, but every feasible point has $s_1\ge\log(1+e^{-\beta})>0$. The value identity is stated for every $\varepsilon\ge0$ and attainment for $\varepsilon>0$.
--
--   **Formalization Note.** $V$ is an abstract finite-dimensional real normed space standing for $(\mathbb R^n,\|\cdot\|)$; $\beta$ is a continuous linear functional on $V$ and $\|\beta\|_*$ its operator norm. Both sides of the identity are computed in $[0,\infty]$; attainment is stated as the existence of a feasible point whose objective value is at most that of every feasible point.
-- source:
--   Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, Distributionally Robust Logistic Regression, Advances in Neural Information Processing Systems 28 (NIPS 2015), p. 4, Theorem 1, eq. (7)

import Mathlib
import Definitions.Def_DRLogReg_Reformulation_Core
import Definitions.Def_DRLogReg_Reformulation_Program

open MeasureTheory
open scoped ENNReal

namespace DRLogReg.Reformulation

/-- Theorem 1 (Tractable Reformulation), Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn,
*Distributionally Robust Logistic Regression*, NIPS 2015, p. 4, eq. (7).

The optimal value `Ĵ = inf_β sup_{Q ∈ B_ε(P̂_N)} E^Q[l_β(x, y)]` of the distributionally robust
problem (6) equals the optimal value of the convex program (7)
`min λε + (1/N) ∑ s_i  s.t.  l_β(x̂_i, ŷ_i) ≤ s_i,  l_β(x̂_i, −ŷ_i) − λκ ≤ s_i,  ‖β‖_* ≤ λ`,
for every radius `ε ≥ 0` and weight `κ > 0`, any norm on the feature space, and `N ≥ 1` samples.
The printed "min" (attainment in (7)) is asserted for `ε > 0`: at `ε = 0` it can fail (with
`V = ℝ`, `N = 1`, `x̂₁ = 1`, `ŷ₁ = +1` the value is `inf_β log(1 + e^{−β}) = 0`, while every
feasible point has `s₁ > 0`). Correction of the printed statement, recorded in the notes. -/
theorem tractable_reformulation
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 ≤ ε) {N : ℕ} (hN : 0 < N)
    (xhat : Fin N → V) (yhat : Fin N → Bool) :
    (⨅ β : V →L[ℝ] ℝ, worstCase κ ε xhat yhat β) = value7 κ ε xhat yhat ∧
      (0 < ε → ∃ p ∈ feasible7 κ xhat yhat, ∀ q ∈ feasible7 κ xhat yhat,
        objective7 ε p ≤ objective7 ε q) := by sorry

end DRLogReg.Reformulation
