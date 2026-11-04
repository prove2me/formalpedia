-- Prove2me | Theorems.Thm_AIMInventory_Known_lemma_13
-- name    : AIMInventory.Known.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:29:36.061612+00:00
-- url     : https://prove2.me/theorems/f1a851d2-a8f2-45a9-8029-4e36d917509a
-- title:
--   Lemma 13 — E|J_{i(θ,t)}(θ)| ≤ E[|J_1(θ)|²]
-- statement:
--   Let $D_1, D_2, \dots$ be i.i.d. nonnegative demands (with finite positive mean), let $\theta > 0$, and let $J_i(\theta)$ be the busy periods of the waiting-time process $W_t(\theta)$, with $i(\theta,t)$ the index of the busy period containing period $t$. For every $t \ge 2$,
--   $$E\,\big|J_{i(\theta,t)}(\theta)\big| \le E\big[|J_1(\theta)|^2\big].$$
--
--   The busy period that covers a fixed time is length-biased; this lemma bounds its mean by the second moment of a typical busy period, which is what makes Lemma 5 a statement about $|J_1(\theta)|$ alone.
--
--   **Formalization Note** Both sides are expectations in $[0,\infty]$, so the statement is meaningful when busy periods can be infinite (then the right side is $+\infty$). Under this mission's indexing ($W_1 = 0$, $\tau_0 = 1$), period $1$ belongs to no busy period, so the paper's "for any $t \ge 1$" becomes $t \ge 2$. The demand law is the mission's `DemandLaw` (finite, positive mean), the paper's standing model.
-- source:
--   Huh & Rusmevichientong, A Non-Parametric Asymptotic Analysis of Inventory Planning with Censored Demand, Math. Oper. Res. (2009), author's manuscript, p. 19, Lemma 13 (Appendix C)

import Mathlib
import Definitions.Def_AIMInventory_Known_Queue
open MeasureTheory
open scoped ENNReal

namespace AIMInventory.Known

/-- Lemma 13, p. 19: the expected length of the busy period containing period `t` is at most the
second moment of the length of the first busy period. -/
theorem lemma_13 (P : CappedBaseStock.DemandLaw) (θ : ℝ) (hθ : 0 < θ) (t : ℕ) (ht : 2 ≤ t) :
    ∫⁻ d, (busyLength θ d (busyIndex θ d t) : ℝ≥0∞) ∂(CappedBaseStock.demandPathLaw P)
      ≤ ∫⁻ d, (busyLength θ d 1 : ℝ≥0∞) ^ 2 ∂(CappedBaseStock.demandPathLaw P) := by sorry

end AIMInventory.Known
