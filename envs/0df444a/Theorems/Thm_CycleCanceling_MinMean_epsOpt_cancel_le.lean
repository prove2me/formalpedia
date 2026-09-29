-- Prove2me | Theorems.Thm_CycleCanceling_MinMean_epsOpt_cancel_le
-- name    : CycleCanceling.MinMean.epsOpt_cancel_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:13:50.516993+00:00
-- url     : https://prove2.me/theorems/b9e00c4e-38e2-4eac-b759-6ab619b7d22b
-- title:
--   Lemma 3.5 — canceling a minimum-mean cycle cannot increase $\varepsilon(f)$
-- statement:
--   Let $f$ be a circulation and let $\Gamma$ be a minimum-mean residual cycle of $f$ with negative cost $c(\Gamma)<0$. Let $f'$ be obtained from $f$ by canceling $\Gamma$, i.e. by pushing the capacity $\delta=\min_{(v,w)\in\Gamma}u_f(v,w)$ of $\Gamma$ around it. Then
--   $$
--   \varepsilon(f')\le\varepsilon(f).
--   $$
--   So $\varepsilon(f)$ is monotone along every run of the minimum-mean cycle-canceling algorithm; this monotonicity is used both in the geometric decrease of Lemma 3.6 and in the arc-fixing argument of Theorem 3.9.
--
--   **Formalization Note** The hypothesis $c(\Gamma)<0$ is the algorithm's context (it cancels only negative cycles); without it the statement fails, since canceling a positive-mean cycle of an optimal circulation can increase $\varepsilon(f)$.
-- source:
--   Goldberg, Tarjan, Finding Minimum-Cost Circulations by Canceling Negative Cycles, J. ACM 36(4), 1989, p. 878, Lemma 3.5

import Mathlib
import Definitions.Def_CycleCanceling_MinMean_Network
import Definitions.Def_CycleCanceling_MinMean_EpsOptimal
import Definitions.Def_CycleCanceling_MinMean_Algorithm

namespace CycleCanceling.MinMean

/-- Lemma 3.5 (p. 878): canceling a minimum-mean cycle cannot increase `ε(f)`. The canceled
cycle `Γ` is, as in the algorithm, a minimum-mean residual cycle of negative cost. -/
theorem epsOpt_cancel_le {V : Type*} [Fintype V] [DecidableEq V]
    (N : CircNetwork V) (f : V → V → ℝ) (hf : IsCirculation N f)
    (Γ : List V) (hΓ : IsMinMeanResidualCycle N f Γ) (hneg : cycleCost N Γ < 0) :
    epsOpt N (cancel N f Γ) ≤ epsOpt N f := by sorry

end CycleCanceling.MinMean
