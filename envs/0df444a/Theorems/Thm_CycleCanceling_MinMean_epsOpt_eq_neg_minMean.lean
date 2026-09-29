-- Prove2me | Theorems.Thm_CycleCanceling_MinMean_epsOpt_eq_neg_minMean
-- name    : CycleCanceling.MinMean.epsOpt_eq_neg_minMean
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:13:02.276661+00:00
-- url     : https://prove2.me/theorems/aa76a2e7-0188-4b03-a832-a923cff9da44
-- title:
--   Theorem 3.3 — for a nonoptimal circulation, $\varepsilon(f) = -\mu(f)$
-- statement:
--   Let $f$ be a circulation that is not minimum-cost, and let $\Gamma$ be a minimum-mean residual cycle of $f$, so that its mean cost $c(\Gamma)/|\Gamma|$ is the minimum cycle mean $\mu(f)$ of the residual graph. Then
--   $$
--   \varepsilon(f)=-\mu(f)=-\frac{c(\Gamma)}{|\Gamma|}.
--   $$
--   This identity, from the authors' earlier work on generalized cost scaling, links the quantity the algorithm optimizes (the minimum cycle mean) with the quality measure used in the analysis ($\varepsilon(f)$); every later step of the analysis uses it.
--
--   **Formalization Note** $\mu(f)$ is represented through an arbitrary witness $\Gamma$: the statement holds for every minimum-mean residual cycle. $\varepsilon(f)$ is the infimum of the set of $\varepsilon\ge0$ for which $f$ is $\varepsilon$-optimal.
-- source:
--   Goldberg, Tarjan, Finding Minimum-Cost Circulations by Canceling Negative Cycles, J. ACM 36(4), 1989, p. 877, Theorem 3.3

import Mathlib
import Definitions.Def_CycleCanceling_MinMean_Network
import Definitions.Def_CycleCanceling_MinMean_EpsOptimal

namespace CycleCanceling.MinMean

/-- Theorem 3.3 (p. 877): if `f` is a nonoptimal circulation then `ε(f) = -μ(f)`, where
`μ(f)` is the mean cost of a minimum-mean residual cycle `Γ` of `f`. -/
theorem epsOpt_eq_neg_minMean {V : Type*} [Fintype V] [DecidableEq V]
    (N : CircNetwork V) (f : V → V → ℝ) (hf : IsCirculation N f) (hnopt : ¬ IsMinCost N f)
    (Γ : List V) (hΓ : IsMinMeanResidualCycle N f Γ) :
    epsOpt N f = -meanCost N Γ := by sorry

end CycleCanceling.MinMean
