-- Prove2me | Theorems.Thm_AddLogReg_LogitBoost_eq_31
-- name    : AddLogReg.LogitBoost.eq_31
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:02:51.515834+00:00
-- url     : https://prove2.me/theorems/9b41d287-8a57-4045-bc9c-9a90d02c4578
-- title:
--   (31), p. 352 — the integrand 2y*t − log(1+e^{2t}) is the Bernoulli log-likelihood of y* under p = e^t/(e^t+e^{−t})
-- statement:
--   Let $y^*\in\{0,1\}$ and $t\in\mathbb R$, and let $p(t) = e^{t}/(e^{t}+e^{-t})$ be the symmetric logistic (30). Then
--   $$2y^*t - \log\big(1+e^{2t}\big) = y^*\log p(t) + (1-y^*)\log\big(1-p(t)\big).$$
--
--   The right-hand side is the Bernoulli log-likelihood of the response $y^*$ when its success probability is $p(t)$. With $t = F(x)+f(x)$ the identity shows that the integrand of (31) is the log-likelihood of the symmetric logistic model, so that $El(F+f)$ in (31) is the expected Bernoulli log-likelihood the Derivation of Result 3 differentiates.
-- source:
--   Friedman, Hastie and Tibshirani, Additive logistic regression: a statistical view of boosting, Ann. Statist. 28 (2000), p. 352, (31); p. 351, (30)

import Mathlib
import Definitions.Def_AddLogReg_LogitBoost_Setting

open MeasureTheory ProbabilityTheory

namespace AddLogReg.LogitBoost

theorem eq_31 (b : Bool) (t : ℝ) :
    2 * ystar b * t - Real.log (1 + Real.exp (2 * t)) =
      ystar b * Real.log (symLogistic t) + (1 - ystar b) * Real.log (1 - symLogistic t) := by sorry

end AddLogReg.LogitBoost
