-- Prove2me | Theorems.Thm_DRLogReg_RiskEstimation_worst_case_risk_lp
-- name    : DRLogReg.RiskEstimation.worst_case_risk_lp
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:39:45.788841+00:00
-- url     : https://prove2.me/theorems/72b61195-8546-490e-8e4b-bee5f548d897
-- title:
--   Theorem 3(i), Eq. (10a) — the worst-case misclassification risk is the optimal value of a linear program
-- statement:
--   Let $V$ be a finite-dimensional real normed space (the feature space $\mathbb R^n$ with an arbitrary norm), $\kappa > 0$, $\varepsilon \ge 0$, $N \ge 1$ training samples $(\hat x_i,\hat y_i)\in V\times\{-1,+1\}$ with empirical distribution $\hat{\mathbb P}_N$, and let $\hat\beta$ be any weight vector, with dual norm $\|\hat\beta\|_*$. Then the linear program (10a),
--   $$\begin{aligned} \min_{\lambda, s_i, r_i, t_i}\ & \lambda\varepsilon + \frac1N\sum_{i=1}^N s_i \\ \text{s.t.}\ & 1 - r_i\hat y_i\langle\hat\beta,\hat x_i\rangle \le s_i,\quad 1 + t_i\hat y_i\langle\hat\beta,\hat x_i\rangle - \lambda\kappa \le s_i, \\ & r_i\|\hat\beta\|_* \le \lambda,\quad t_i\|\hat\beta\|_* \le \lambda,\quad r_i,t_i,s_i \ge 0 \qquad \forall i\le N, \end{aligned}$$
--   attains its minimum $v$, and
--   $$\mathfrak R_{\max}(\hat\beta) = \sup_{\mathbb Q\in\mathbb B_\varepsilon(\hat{\mathbb P}_N)}\mathbb E^{\mathbb Q}\big[\mathbb 1_{\{y\langle\hat\beta,x\rangle\le 0\}}\big] = v.$$
--
--   The worst-case probability of a nonpositive margin over an infinite-dimensional ambiguity set is thus computed by a linear program with $3N+1$ variables.
--
--   **Formalization Note.** $\hat\beta$ is any continuous linear functional (the identity does not depend on how $\hat\beta$ was computed from the data); $\|\hat\beta\|_*$ is its operator norm. "min" is formalized as `IsLeast` of the image of the feasible set under the objective, and the supremum is taken in $[0,\infty]$ over the probability measures of the ball.
-- source:
--   Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, Distributionally Robust Logistic Regression, Advances in Neural Information Processing Systems 28 (NIPS 2015), p. 5, Theorem 3(i), Eq. (10a)

import Mathlib
import Definitions.Def_DRLogReg_RiskEstimation_Core
import Definitions.Def_DRLogReg_RiskEstimation_Risk
import Definitions.Def_DRLogReg_RiskEstimation_Program

open MeasureTheory
open scoped ENNReal

namespace DRLogReg.RiskEstimation

/-- Theorem 3(i), eq. (10a) (Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, NIPS 2015, p. 5):
for every `ε ≥ 0`, `κ > 0`, `N ≥ 1` training samples `(x̂_i, ŷ_i)` and every weight vector `β̂`,
the linear program (10a) attains its minimum `v`, and the worst-case risk
`R_max(β̂) = sup_{Q ∈ B_ε(P̂_N)} E^Q[1{y⟨β̂, x⟩ ≤ 0}]` equals `v`. The feature space is `V`, a
finite-dimensional real normed space with an arbitrary norm; `‖β̂‖_*` is the operator norm. -/
theorem worst_case_risk_lp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (κ ε : ℝ) (hκ : 0 < κ) (hε : 0 ≤ ε) {N : ℕ} (hN : 0 < N)
    (xhat : Fin N → V) (yhat : Fin N → Bool) (βhat : V →L[ℝ] ℝ) :
    ∃ v : ℝ, IsLeast (objective10 ε '' feasible10a κ xhat yhat βhat) v ∧
      riskMax κ ε xhat yhat βhat = ENNReal.ofReal v := by sorry

end DRLogReg.RiskEstimation
