-- Prove2me | Theorems.Thm_DRLogReg_RiskEstimation_best_case_risk_confidence
-- name    : DRLogReg.RiskEstimation.best_case_risk_confidence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:41:06.710227+00:00
-- url     : https://prove2.me/theorems/2f76ba39-8725-4260-91db-a87faf6e6be5
-- title:
--   Theorem 3(ii), confidence clause — R_min(β̂) ≤ R(β̂) with probability at least 1 − η (given Theorem 2's event)
-- statement:
--   Let $\mathbb P$ be a probability distribution on $\Xi = V\times\{-1,+1\}$, $\kappa>0$, $\varepsilon\ge0$, $0<\eta\le1$ and $N\ge1$. Draw $N$ i.i.d. training samples from $\mathbb P$, form their empirical distribution $\hat{\mathbb P}_N$, and let $\hat\beta$ be any weight vector computed from the sample. Assume
--   $$\mathbb P^N\big\{\mathbb P \in \mathbb B_\varepsilon(\hat{\mathbb P}_N)\big\} \ge 1-\eta,$$
--   which is what Theorem 2 (p. 4) guarantees when $\varepsilon = \varepsilon_N(\eta)$ from (8). Then
--   $$\mathbb P^N\big\{\mathfrak R_{\min}(\hat\beta) \le \mathfrak R(\hat\beta)\big\} \ge 1-\eta.$$
--
--   The best-case risk is therefore a lower confidence bound on the out-of-sample misclassification probability.
--
--   **Formalization Note.** As for part (i): Theorem 2's conclusion is a hypothesis, "with probability $1-\eta$" means "at least $1-\eta$", and $\mathbb P^N$ is `Measure.pi` applied as an outer measure.
-- source:
--   Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, Distributionally Robust Logistic Regression, Advances in Neural Information Processing Systems 28 (NIPS 2015), p. 6, Theorem 3(ii), confidence clause

import Mathlib
import Definitions.Def_DRLogReg_RiskEstimation_Core
import Definitions.Def_DRLogReg_RiskEstimation_Risk

open MeasureTheory
open scoped ENNReal

namespace DRLogReg.RiskEstimation

/-- Theorem 3(ii), confidence clause (Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, NIPS 2015,
p. 6): "If the Wasserstein radius ε is set to ε_N(η) as defined in (8), then R_min(β̂) ≤ R(β̂) with
probability 1 − η across all training sets." The radius ε_N(η) enters only through the conclusion
of Theorem 2 (p. 4), `P^N{P ∈ B_ε(P̂_N)} ≥ 1 − η`, which is taken here as the hypothesis `hconc`;
the concentration inequality itself is not part of this statement. The training samples are
`N` i.i.d. draws `ξs` from the probability measure `P` on `Ξ`, `β̂ = βhat ξs` is an arbitrary
function of the sample, and "with probability 1 − η" is read as "with probability at least
1 − η". -/
theorem best_case_risk_confidence {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (κ ε η : ℝ) (hκ : 0 < κ) (hε : 0 ≤ ε) (hη₀ : 0 < η) (hη₁ : η ≤ 1)
    {N : ℕ} (hN : 0 < N) (P : Measure (V × Bool)) [IsProbabilityMeasure P]
    (βhat : (Fin N → V × Bool) → V →L[ℝ] ℝ)
    (hconc : ENNReal.ofReal (1 - η) ≤ Measure.pi (fun _ : Fin N => P)
      {ξs | P ∈ wassersteinBall κ ε (empirical (fun i => (ξs i).1) (fun i => (ξs i).2))}) :
    ENNReal.ofReal (1 - η) ≤ Measure.pi (fun _ : Fin N => P)
      {ξs | riskMin κ ε (fun i => (ξs i).1) (fun i => (ξs i).2) (βhat ξs) ≤ risk P (βhat ξs)} := by sorry

end DRLogReg.RiskEstimation
