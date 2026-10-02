-- Prove2me | Theorems.Thm_DRLogReg_RiskEstimation_risk_two_sided_confidence
-- name    : DRLogReg.RiskEstimation.risk_two_sided_confidence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:41:54.28346+00:00
-- url     : https://prove2.me/theorems/f135b553-b1bd-4c93-810b-1c84d4e50110
-- title:
--   §3.3, p. 6 — R_min(β̂) ≤ R(β̂) ≤ R_max(β̂) with probability at least 1 − 2η (given Theorem 2's event)
-- statement:
--   Under the hypotheses of the confidence clauses of Theorem 3 — a probability distribution $\mathbb P$ on $\Xi$, $\kappa>0$, $\varepsilon\ge0$, $0<\eta\le1$, $N\ge1$ i.i.d. samples from $\mathbb P$, a sample-dependent weight vector $\hat\beta$, and $\mathbb P^N\{\mathbb P\in\mathbb B_\varepsilon(\hat{\mathbb P}_N)\}\ge 1-\eta$ — the true misclassification risk is bracketed by the best- and worst-case risks:
--   $$\mathbb P^N\big\{\mathfrak R_{\min}(\hat\beta) \le \mathfrak R(\hat\beta) \le \mathfrak R_{\max}(\hat\beta)\big\} \ge 1-2\eta.$$
--
--   Together with Theorem 3's identities, this gives a two-sided confidence interval for the misclassification risk computable by two linear programs.
--
--   **Formalization Note.** The level is the printed $1-2\eta$, which is $0$ (hence the statement is empty) when $\eta \ge 1/2$. Theorem 2's conclusion is a hypothesis, and $\mathbb P^N$ is `Measure.pi` applied as an outer measure.
-- source:
--   Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, Distributionally Robust Logistic Regression, Advances in Neural Information Processing Systems 28 (NIPS 2015), p. 6, §3.3, sentence after Theorem 3

import Mathlib
import Definitions.Def_DRLogReg_RiskEstimation_Core
import Definitions.Def_DRLogReg_RiskEstimation_Risk

open MeasureTheory
open scoped ENNReal

namespace DRLogReg.RiskEstimation

/-- §3.3 (Shafieezadeh-Abadeh, Mohajerin Esfahani & Kuhn, NIPS 2015, p. 6): "Moreover, we have
R_min(β̂) ≤ R(β̂) ≤ R_max(β̂) with probability 1 − 2η." As in Theorem 3, the radius ε_N(η) enters
only through the conclusion of Theorem 2 (p. 4), `P^N{P ∈ B_ε(P̂_N)} ≥ 1 − η`, taken here as the
hypothesis `hconc`. The training samples are `N` i.i.d. draws `ξs` from `P`, `β̂ = βhat ξs` is an
arbitrary function of the sample, and "with probability 1 − 2η" is read as "with probability at
least 1 − 2η" (the printed level; for `η > 1/2` it is `0`). -/
theorem risk_two_sided_confidence {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (κ ε η : ℝ) (hκ : 0 < κ) (hε : 0 ≤ ε) (hη₀ : 0 < η) (hη₁ : η ≤ 1)
    {N : ℕ} (hN : 0 < N) (P : Measure (V × Bool)) [IsProbabilityMeasure P]
    (βhat : (Fin N → V × Bool) → V →L[ℝ] ℝ)
    (hconc : ENNReal.ofReal (1 - η) ≤ Measure.pi (fun _ : Fin N => P)
      {ξs | P ∈ wassersteinBall κ ε (empirical (fun i => (ξs i).1) (fun i => (ξs i).2))}) :
    ENNReal.ofReal (1 - 2 * η) ≤ Measure.pi (fun _ : Fin N => P)
      {ξs | riskMin κ ε (fun i => (ξs i).1) (fun i => (ξs i).2) (βhat ξs) ≤ risk P (βhat ξs) ∧
        risk P (βhat ξs) ≤ riskMax κ ε (fun i => (ξs i).1) (fun i => (ξs i).2) (βhat ξs)} := by sorry

end DRLogReg.RiskEstimation
