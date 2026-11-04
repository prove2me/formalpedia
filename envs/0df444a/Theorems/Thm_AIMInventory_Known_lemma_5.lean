-- Prove2me | Theorems.Thm_AIMInventory_Known_lemma_5
-- name    : AIMInventory.Known.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:29:51.60538+00:00
-- url     : https://prove2.me/theorems/031714ea-e174-4be5-b53d-b5f4ae1973c5
-- title:
--   Lemma 5 — E[Σ_{t=1}^T Z_t(θ)] ≤ 2θ E[|J_1(θ)|²] √T
-- statement:
--   Let $D_1, D_2, \dots$ be i.i.d. nonnegative demands (with finite positive mean), let $\theta > 0$, let $Z_t(\theta)$ be the queue with $Z_1(\theta) = 0$ and $Z_{t+1}(\theta) = [Z_t(\theta) + \theta/\sqrt t - D_t]^+$, and let $J_1(\theta)$ be the first busy period of Lindley's waiting-time process $W_{t+1}(\theta) = [W_t(\theta) + \theta - D_t]^+$, $W_1(\theta) = 0$. For every $T \ge 1$,
--   $$E\Big[\sum_{t=1}^T Z_t(\theta)\Big] \le 2\theta\, E\big[|J_1(\theta)|^2\big]\,\sqrt T .$$
--
--   Combined with Theorem 6 at $\theta = \rho$, this bounds the average excess cost of non-perishable AIM by $2h\rho E[|J_1(\rho)|^2]/\sqrt T$.
--
--   **Formalization Note** Both sides are expectations in $[0,\infty]$ (the left side as a lower Lebesgue integral of the nonnegative sum, the right side as $2\theta\sqrt T$ times the lower Lebesgue integral of $|J_1(\theta)|^2$), so the bound is meaningful when $E[|J_1(\theta)|^2] = +\infty$. Indexing: $W_1 = Z_1 = 0$, $\tau_0 = 1$, as in the mission's queue definitions.
-- source:
--   Huh & Rusmevichientong, A Non-Parametric Asymptotic Analysis of Inventory Planning with Censored Demand, Math. Oper. Res. (2009), author's manuscript, p. 9, Lemma 5 (proof in Appendix C, pp. 19–20)

import Mathlib
import Definitions.Def_AIMInventory_Known_Queue
open MeasureTheory
open scoped ENNReal

namespace AIMInventory.Known

/-- Lemma 5, p. 9: `E[Σ_{t=1}^T Z_t(θ)] ≤ 2θ E[|J_1(θ)|²] √T` for every `θ > 0` and `T ≥ 1`. -/
theorem lemma_5 (P : CappedBaseStock.DemandLaw) (θ : ℝ) (hθ : 0 < θ) (T : ℕ) (hT : 1 ≤ T) :
    ∫⁻ d, ENNReal.ofReal (∑ t ∈ Finset.Icc 1 T, auxQueue θ d t) ∂(CappedBaseStock.demandPathLaw P)
      ≤ ENNReal.ofReal (2 * θ * Real.sqrt T) *
          ∫⁻ d, (busyLength θ d 1 : ℝ≥0∞) ^ 2 ∂(CappedBaseStock.demandPathLaw P) := by sorry

end AIMInventory.Known
