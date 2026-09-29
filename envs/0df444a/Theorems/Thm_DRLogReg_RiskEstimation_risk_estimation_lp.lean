-- Prove2me | Theorems.Thm_DRLogReg_RiskEstimation_risk_estimation_lp
-- name    : DRLogReg.RiskEstimation.risk_estimation_lp
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:42:39.235481+00:00
-- url     : https://prove2.me/theorems/36f78971-0475-437c-96d7-87f8e495675d
-- title:
--   Theorem 3 (Risk Estimation), (i)–(ii) — worst- and best-case misclassification risks over a Wasserstein ball via the LPs (10a)–(10b)
-- statement:
--   Let $V$ be a finite-dimensional real normed space (the feature space $\mathbb R^n$ with an arbitrary norm $\|\cdot\|$), $\kappa>0$, $\varepsilon\ge 0$, and $(\hat x_i,\hat y_i)_{i=1}^N$ with $N \ge 1$ training samples in $\Xi = V\times\{-1,+1\}$, with empirical distribution $\hat{\mathbb P}_N$. The Wasserstein ball $\mathbb B_\varepsilon(\hat{\mathbb P}_N)$ is taken with respect to $d((x,y),(x',y')) = \|x-x'\| + \kappa|y-y'|/2$. For every weight vector $\hat\beta$, in particular every $\hat\beta$ depending on the training data:
--
--   1. The linear program (10a) attains its minimum $v$, and the worst-case risk equals it:
--   $$\mathfrak R_{\max}(\hat\beta) := \sup_{\mathbb Q\in\mathbb B_\varepsilon(\hat{\mathbb P}_N)}\mathbb E^{\mathbb Q}\big[\mathbb 1_{\{y\langle\hat\beta,x\rangle\le0\}}\big] = v.$$
--   2. The linear program (10b) attains its minimum $w$, and the best-case risk satisfies
--   $$\mathfrak R_{\min}(\hat\beta) := \inf_{\mathbb Q\in\mathbb B_\varepsilon(\hat{\mathbb P}_N)}\mathbb E^{\mathbb Q}\big[\mathbb 1_{\{y\langle\hat\beta,x\rangle<0\}}\big] = 1 - w.$$
--
--   Here (10a) and (10b) minimize $\lambda\varepsilon + \frac1N\sum_i s_i$ over $(\lambda,s,r,t)\in\mathbb R\times\mathbb R^N\times\mathbb R^N\times\mathbb R^N$ subject to, for all $i$, $1 \mp r_i\hat y_i\langle\hat\beta,\hat x_i\rangle \le s_i$, $1 \pm t_i\hat y_i\langle\hat\beta,\hat x_i\rangle - \lambda\kappa \le s_i$, $r_i\|\hat\beta\|_*\le\lambda$, $t_i\|\hat\beta\|_*\le\lambda$, $r_i,t_i,s_i\ge0$ (upper signs for (10a), lower signs for (10b)).
--
--   This turns the extremal misclassification probabilities over an infinite-dimensional Wasserstein ambiguity set into two finite linear programs, which yield confidence bounds on the out-of-sample misclassification risk of any classifier $\hat\beta$.
--
--   **Formalization Note.** $\hat\beta$ is a continuous linear functional `V →L[ℝ] ℝ` and $\|\hat\beta\|_*$ its operator norm (the dual norm). "min" is `IsLeast` of the objective's image of the feasible set; the supremum and infimum range over the probability measures in the ball and are taken in $[0,\infty]$; both LP values lie in $[0,1]$. The confidence clauses of Theorem 3 are separate milestones.
-- source:
--   Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, Distributionally Robust Logistic Regression, Advances in Neural Information Processing Systems 28 (NIPS 2015), p. 5, Theorem 3 (i)–(ii), Eqs. (10a) and (10b)

import Mathlib
import Definitions.Def_DRLogReg_RiskEstimation_Core
import Definitions.Def_DRLogReg_RiskEstimation_Risk
import Definitions.Def_DRLogReg_RiskEstimation_Program

open MeasureTheory
open scoped ENNReal

namespace DRLogReg.RiskEstimation

/-- Theorem 3 (Risk Estimation), parts (i) and (ii), eqs. (10a) and (10b)
(Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, NIPS 2015, p. 5): for every `ε ≥ 0`, `κ > 0`,
`N ≥ 1` training samples `(x̂_i, ŷ_i)` and every weight vector `β̂` (in particular any `β̂`
computed from the training data),
(i) the linear program (10a) attains its minimum `v` and the worst-case risk
`R_max(β̂) = sup_{Q ∈ B_ε(P̂_N)} E^Q[1{y⟨β̂, x⟩ ≤ 0}]` equals `v`;
(ii) the linear program (10b) attains its minimum `w` and the best-case risk
`R_min(β̂) = inf_{Q ∈ B_ε(P̂_N)} E^Q[1{y⟨β̂, x⟩ < 0}]` equals `1 − w`.
The feature space is `V`, a finite-dimensional real normed space with an arbitrary norm;
`‖β̂‖_*` is the operator norm. -/
theorem risk_estimation_lp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (κ ε : ℝ) (hκ : 0 < κ) (hε : 0 ≤ ε) {N : ℕ} (hN : 0 < N)
    (xhat : Fin N → V) (yhat : Fin N → Bool) (βhat : V →L[ℝ] ℝ) :
    (∃ v : ℝ, IsLeast (objective10 ε '' feasible10a κ xhat yhat βhat) v ∧
      riskMax κ ε xhat yhat βhat = ENNReal.ofReal v) ∧
    (∃ w : ℝ, IsLeast (objective10 ε '' feasible10b κ xhat yhat βhat) w ∧
      riskMin κ ε xhat yhat βhat = ENNReal.ofReal (1 - w)) := by sorry

end DRLogReg.RiskEstimation
