-- Prove2me | Theorems.Thm_DevContest_eq_EC_42_value_duration
-- name    : DevContest.eq_EC_42_value_duration
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:54:37.899311+00:00
-- url     : https://prove2.me/theorems/d30d9502-0ece-4d72-9cd9-eb7b1087eff3
-- title:
--   Display (EC.42) — the leader's value is $(\lambda\bar R-c)$ times the expected duration
-- statement:
--   Let $\lambda,c>0$ and $2c/\lambda<\bar R<3c/\lambda$. Let $y$ be a measurable effort of the laggard, with values in $[0,1]$, and let $s\ge0$. With the leader at full effort and both agents at full effort after a catch-up,
--   $$
--   V_{1,0}=(\lambda\bar R-c)\,T_{1,0},
--   $$
--   where $V_{1,0}$ is the leader's expected continuation payoff from her first success at $s$ and $T_{1,0}$ is the expected time from $s$ to the end of the contest.
--
--   So, along a contest, a leader's surplus measures the remaining duration.
--
--   Differences from the source:
--   - encoding: $V_{1,0,p}$ and $T_{1,0,p}$ given by the two integrals of (EC.42) → expectations of the realized payoff and duration over independent clocks; reason: the integrals on the page evaluate the same expectations
--   - encoding: a stage succeeds at a Poisson arrival with instantaneous probability $\lambda x$ → a stage ends when $\int\lambda x$ reaches an independent unit-exponential clock; reason: this is the standard time change of the same point process; it has the same law for every effort path
-- source:
--   Khorasani, Körpeoğlu, Krishnan, Dynamic Development Contests, author manuscript, display (EC.42), p.ec19

import Mathlib
import Definitions.Def_DevContest_leaderRace

open scoped NNReal

namespace DevContest

/-- Display (EC.42), Khorasani, Körpeoğlu, Krishnan, *Dynamic Development Contests*, author
manuscript, p.ec19: `V_{1,0,p} = (λ R̄ - c) T_{1,0,p}`, for the leader's continuation payoff and the
expected duration, both expectations over the clocks, with the leader at full effort, an arbitrary
deterministic measurable laggard effort `y`, and both at full effort after a catch-up. -/
theorem eq_EC_42_value_duration {lam c Rbar : ℝ} (hlam : 0 < lam) (hc : 0 < c)
    (hlow : 2 * c / lam < Rbar) (hhigh : Rbar < 3 * c / lam) {y : ℝ≥0 → ℝ} (hy : Measurable y)
    (hy01 : ∀ t, y t ∈ Set.Icc (0 : ℝ) 1) (s : ℝ≥0) :
    leaderValue lam c Rbar y s = (lam * Rbar - c) * leaderDuration lam y s := by sorry

end DevContest
