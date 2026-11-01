-- Prove2me | Theorems.Thm_DevContest_one_success_full_effort
-- name    : DevContest.one_success_full_effort
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:52:57.10035+00:00
-- url     : https://prove2.me/theorems/af7dc91f-8164-48d2-b75e-b2a851475f8e
-- title:
--   Proof of Theorem 2, p.ec17 — an agent with one success finds full effort optimal
-- statement:
--   Let $\lambda,c>0$ and $2c/\lambda<\bar R<3c/\lambda$. Consider any disclosure policy, any admissible strategy of the rival of agent $i$, and any admissible strategy $y$ of agent $i$. Let $y'$ be the strategy that follows $y$ until $i$'s first success and exerts full effort from then on. Then $y'$ is admissible for $i$, and it gives $i$ an expected utility at least as high as $y$.
--
--   Thus no agent ever loses by working at full speed after her first success.
--
--   Differences from the source:
--   - generalization: stated in the proof of Theorem 2, for PCSD with the equilibrium rival → every policy, every admissible rival strategy and every admissible strategy of $i$; reason: §5.1, p.17 says such an agent exerts full effort irrespective of the policy; PCSD is one instance
-- source:
--   Khorasani, Körpeoğlu, Krishnan, Dynamic Development Contests, author manuscript, Proof of Theorem 2, p.ec17; §5.1, p.17

import Mathlib
import Definitions.Def_DevContest_payoff

open scoped ENNReal NNReal

namespace DevContest

/-- Khorasani, Körpeoğlu, Krishnan, *Dynamic Development Contests*, author manuscript, p.ec17: an
agent with one success finds it optimal to spend full effort at all times. For every policy, every
admissible rival strategy and every admissible strategy `y` of agent `i`, replacing `y` by full
effort from `i`'s first success on stays admissible and does not lower `i`'s payoff. -/
theorem one_success_full_effort {lam c Rbar : ℝ} (hlam : 0 < lam) (hc : 0 < c)
    (hlow : 2 * c / lam < Rbar) (hhigh : Rbar < 3 * c / lam)
    {U M : Type} [MeasurableSpace U] (D : Policy U M) (x : Fin 2 → Strategy U) (i : Fin 2)
    (hx : IsAdmissible D (rival i) (x (rival i))) (y : Strategy U) (hy : IsAdmissible D i y) :
    let y' : Strategy U := fun t r u => if r i ≤ (t : ℝ≥0∞) then 1 else y t r u
    IsAdmissible D i y' ∧
      payoff lam c Rbar D (Function.update x i y) i ≤
        payoff lam c Rbar D (Function.update x i y') i := by sorry

end DevContest
