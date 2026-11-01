-- Prove2me | Theorems.Thm_DevContest_pcsd_belief_bayes
-- name    : DevContest.pcsd_belief_bayes
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:53:12.992981+00:00
-- url     : https://prove2.me/theorems/bce6c847-1e9c-4ae8-9c09-0afcf30d2e5b
-- title:
--   Bayes step, p.ec17 — under PCSD, $p_t$ is the conditional probability that the rival has succeeded
-- statement:
--   Let $\lambda,c>0$ and $2c/\lambda<\bar R<3c/\lambda$, and consider PCSD with its equilibrium strategies. Fix an agent $i$ and a date $t$. Let $E$ be the event that $i$ has no success by $t$, the contest has not ended by $t$, and $i$ has received no message by $t$. Then $\mathbb P(E)>0$ and
--   $$
--   \mathbb P\bigl(-i\text{ has succeeded by }t\mid E\bigr)=p_t .
--   $$
--   So the path $p_t$ of Theorem 2 is the agent's actual posterior belief, and this ties the closed form to the model.
--
--   Differences from the source:
--   - encoding: the belief is recursively updated over intervals $(t,t+dt)$, with $\phi_t$ the probability of disclosure → the belief is the conditional probability at date $t$ under the law of the contest; reason: the recursion on p.ec17 computes this conditional probability
--   - encoding: a stage succeeds at a Poisson arrival with instantaneous probability $\lambda x$ → a stage ends when $\int\lambda x$ reaches an independent unit-exponential clock; reason: this is the standard time change of the same point process; it has the same law for every effort path
-- source:
--   Khorasani, Körpeoğlu, Krishnan, Dynamic Development Contests, author manuscript, Bayes step, p.ec17; display (9), p.21; Theorem 2, p.22

import Mathlib
import Definitions.Def_DevContest_payoff
import Definitions.Def_DevContest_pcsd

open scoped ENNReal NNReal
open MeasureTheory

namespace DevContest

/-- The Bayes step of Khorasani, Körpeoğlu, Krishnan, *Dynamic Development Contests*, author
manuscript, p.ec17, in the model: under PCSD and its equilibrium strategies, `pcsdBelief lam c Rbar t`
is the conditional probability, given that agent `i` has no success by `t`, that the contest has not
ended by `t` and that `i` has received no message by `t`, that her rival has succeeded by `t`. The
conditioning event has positive probability. -/
theorem pcsd_belief_bayes {lam c Rbar : ℝ} (hlam : 0 < lam) (hc : 0 < c)
    (hlow : 2 * c / lam < Rbar) (hhigh : Rbar < 3 * c / lam) (i : Fin 2) (t : ℝ≥0) :
    let P := law (pcsd lam c Rbar)
    let O : unitInterval × Clocks → Outcome := fun ω => play lam (pcsdEffort lam c Rbar) ω.1 ω.2
    let E : Set (unitInterval × Clocks) := {ω | (t : ℝ≥0∞) < (O ω).first i ∧ (t : ℝ≥0∞) < (O ω).lead ∧
      (pcsd lam c Rbar).sig t (O ω).first ω.1 i = none}
    let A : Set (unitInterval × Clocks) := {ω | (O ω).first (rival i) ≤ (t : ℝ≥0∞)}
    0 < P.real E ∧ P.real (A ∩ E) / P.real E = pcsdBelief lam c Rbar t := by sorry

end DevContest
