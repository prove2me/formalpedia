-- Prove2me | Theorems.Thm_DRLogReg_RiskEstimation_worst_case_risk_confidence
-- name    : DRLogReg.RiskEstimation.worst_case_risk_confidence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:40:25.378641+00:00
-- url     : https://prove2.me/theorems/50f60a52-2824-4861-9586-78a18b600cce
-- title:
--   Theorem 3(i), confidence clause — R_max(β̂) ≥ R(β̂) with probability at least 1 − η (given Theorem 2's event)
-- statement:
--   Let $\mathbb P$ be a probability distribution on $\Xi = V\times\{-1,+1\}$, $\kappa>0$, $\varepsilon\ge0$, $0<\eta\le1$ and $N\ge1$. Draw $N$ i.i.d. training samples $\xi_1,\dots,\xi_N$ from $\mathbb P$, form their empirical distribution $\hat{\mathbb P}_N$, and let $\hat\beta = \hat\beta(\xi_1,\dots,\xi_N)$ be any weight vector computed from the sample. Assume
--   $$\mathbb P^N\big\{\mathbb P \in \mathbb B_\varepsilon(\hat{\mathbb P}_N)\big\} \ge 1-\eta,$$
--   which is what Theorem 2 (p. 4) guarantees when $\varepsilon = \varepsilon_N(\eta)$ from (8). Then
--   $$\mathbb P^N\big\{\mathfrak R_{\max}(\hat\beta) \ge \mathfrak R(\hat\beta)\big\} \ge 1-\eta,$$
--   where $\mathfrak R(\hat\beta) = \mathbb P[y \ne f_{\hat\beta}(x)]$ is the true misclassification risk.
--
--   The worst-case risk is therefore an upper confidence bound on the out-of-sample misclassification probability.
--
--   **Formalization Note.** The concentration inequality of Theorem 2 (the choice $\varepsilon = \varepsilon_N(\eta)$) is not formalized in this mission; its conclusion enters as the hypothesis above. "With probability $1-\eta$" is read as "with probability at least $1-\eta$". $\mathbb P^N$ is the product measure `Measure.pi`, applied to the event as an outer measure (no measurability of $\hat\beta$ is assumed).
-- source:
--   Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, Distributionally Robust Logistic Regression, Advances in Neural Information Processing Systems 28 (NIPS 2015), p. 5, Theorem 3(i), confidence clause

import Mathlib
import Definitions.Def_DRLogReg_RiskEstimation_Core
import Definitions.Def_DRLogReg_RiskEstimation_Risk

open MeasureTheory
open scoped ENNReal

namespace DRLogReg.RiskEstimation

/-- Theorem 3(i), confidence clause (Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, NIPS 2015,
p. 5): "If the Wasserstein radius ε is set to ε_N(η) as defined in (8), then R_max(β̂) ≥ R(β̂) with
probability 1 − η across all training sets." The radius ε_N(η) enters only through the conclusion
of Theorem 2 (p. 4), `P^N{P ∈ B_ε(P̂_N)} ≥ 1 − η`, which is taken here as the hypothesis `hconc`;
the concentration inequality itself is not part of this statement. The training samples are
`N` i.i.d. draws `ξs` from the probability measure `P` on `Ξ`, `β̂ = βhat ξs` is an arbitrary
function of the sample, and "with probability 1 − η" is read as "with probability at least
1 − η". -/
theorem worst_case_risk_confidence {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (κ ε η : ℝ) (hκ : 0 < κ) (hε : 0 ≤ ε) (hη₀ : 0 < η) (hη₁ : η ≤ 1)
    {N : ℕ} (hN : 0 < N) (P : Measure (V × Bool)) [IsProbabilityMeasure P]
    (βhat : (Fin N → V × Bool) → V →L[ℝ] ℝ)
    (hconc : ENNReal.ofReal (1 - η) ≤ Measure.pi (fun _ : Fin N => P)
      {ξs | P ∈ wassersteinBall κ ε (empirical (fun i => (ξs i).1) (fun i => (ξs i).2))}) :
    ENNReal.ofReal (1 - η) ≤ Measure.pi (fun _ : Fin N => P)
      {ξs | risk P (βhat ξs) ≤ riskMax κ ε (fun i => (ξs i).1) (fun i => (ξs i).2) (βhat ξs)} := by sorry

end DRLogReg.RiskEstimation
