-- Prove2me | Theorems.Thm_DevContest_pcsd_equilibrium
-- name    : DevContest.pcsd_equilibrium
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:54:19.609482+00:00
-- url     : https://prove2.me/theorems/8d9af28e-005a-4956-9ca2-56945f3d724d
-- title:
--   Theorem 2 (Equilibrium) — the stated strategies are a Nash equilibrium under PCSD; half of the goal
-- statement:
--   Let $\lambda,c>0$ and $2c/\lambda<\bar R<3c/\lambda$. Under PCSD, the strategies in which an agent with no success exerts full effort until she obtains her first success, or her opponent obtains her second success, or the principal discloses the opponent's partial progress, and an agent with one success exerts full effort until the end, form a Nash equilibrium.
--
--   This is the first half of the proof of Theorem 2, and the first conjunct of the mission's goal theorem.
--
--   Differences from the source:
--   - reading: equilibrium → Nash equilibrium against every admissible deviation, in expected utility from time $0$; reason: the paper derives a pure-strategy Nash equilibrium, p.ec1
--   - encoding: a stage succeeds at a Poisson arrival with instantaneous probability $\lambda x$ → a stage ends when $\int\lambda x$ reaches an independent unit-exponential clock; reason: this is the standard time change of the same point process; it has the same law for every effort path
-- source:
--   Khorasani, Körpeoğlu, Krishnan, Dynamic Development Contests, author manuscript, Theorem 2 (Equilibrium), p.22; proof, pp.ec17–ec18

import Mathlib
import Definitions.Def_DevContest_IsNash
import Definitions.Def_DevContest_pcsd

namespace DevContest

/-- The (Equilibrium) clause of Theorem 2, Khorasani, Körpeoğlu, Krishnan, *Dynamic Development
Contests*, author manuscript, p.22: under PCSD the strategies `pcsdEffort` form a Nash equilibrium.
This restates the first conjunct of the mission's goal. -/
theorem pcsd_equilibrium {lam c Rbar : ℝ} (hlam : 0 < lam) (hc : 0 < c)
    (hlow : 2 * c / lam < Rbar) (hhigh : Rbar < 3 * c / lam) :
    IsNash lam c Rbar (pcsd lam c Rbar) (pcsdEffort lam c Rbar) := by sorry

end DevContest
