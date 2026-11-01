-- Prove2me | Theorems.Thm_DevContest_eq_EC_41_values
-- name    : DevContest.eq_EC_41_values
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:54:39.958476+00:00
-- url     : https://prove2.me/theorems/afbcadae-b038-45da-bbf5-32b8bcfcf8fe
-- title:
--   Display (EC.41) — the continuation payoffs $V_{1,1}$ and $V_{1,0}$
-- statement:
--   Let $\lambda,c>0$, $2c/\lambda<\bar R<3c/\lambda$, and let $t\ge0$. Computed as expectations over the clocks, with all the efforts of the pages:
--
--   1. $V_{1,1}=\tfrac12(\bar R-c/\lambda)$, when both agents are in the second stage;
--   2. $V_{1,0}=\bar R-c/\lambda$ when the rival has quit, which is the case after a disclosure;
--   3. $V_{1,0}=\tfrac34(\bar R-c/\lambda)$ when the rival keeps working.
--
--   Consequently
--   $$
--   V^\phi_{1,t}=p_t\cdot\tfrac12\Bigl(\bar R-\frac c\lambda\Bigr)+(1-p_t)\Bigl[\phi^*_t\Bigl(\bar R-\frac c\lambda\Bigr)+(1-\phi^*_t)\tfrac34\Bigl(\bar R-\frac c\lambda\Bigr)\Bigr].
--   $$
--   These are the numbers from which $\phi^*$ is designed.
--
--   Differences from the source:
--   - encoding: $V_{1,1}$ and $V_{1,0}$ given by an integral over $\tau$ → expectations of the realized reward and cost over independent clocks; reason: the integral on the page evaluates the same expectation
--   - encoding: a stage succeeds at a Poisson arrival with instantaneous probability $\lambda x$ → a stage ends when $\int\lambda x$ reaches an independent unit-exponential clock; reason: this is the standard time change of the same point process; it has the same law for every effort path
-- source:
--   Khorasani, Körpeoğlu, Krishnan, Dynamic Development Contests, author manuscript, display (EC.41), p.ec18

import Mathlib
import Definitions.Def_DevContest_leaderRace

open scoped NNReal

namespace DevContest

/-- The continuation payoffs of display (EC.41), Khorasani, Körpeoğlu, Krishnan, *Dynamic Development
Contests*, author manuscript, p.ec18, computed as expectations over the clocks: `V_{1,1} = ½(R̄-c/λ)`
when both agents are in the second stage; `R̄ - c/λ` for a leader whose rival has quit, which is the
case after a disclosure; `¾(R̄-c/λ)` for a leader whose rival keeps working. Hence
`V^φ_{1,p} = p V_{1,1} + (1-p) V^φ_{1,0}` with `V^φ_{1,0} = φ(R̄-c/λ) + (1-φ)¾(R̄-c/λ)`. -/
theorem eq_EC_41_values {lam c Rbar : ℝ} (hlam : 0 < lam) (hc : 0 < c)
    (hlow : 2 * c / lam < Rbar) (hhigh : Rbar < 3 * c / lam) (t : ℝ≥0) :
    bothValue lam c Rbar t = 1 / 2 * (Rbar - c / lam) ∧
    leaderValue lam c Rbar (fun _ => 0) t = Rbar - c / lam ∧
    leaderValue lam c Rbar (fun _ => 1) t = 3 / 4 * (Rbar - c / lam) ∧
    pcsdContinuation lam c Rbar t =
      pcsdBelief lam c Rbar t * (1 / 2 * (Rbar - c / lam)) +
        (1 - pcsdBelief lam c Rbar t) *
          (phiStar lam c Rbar t * (Rbar - c / lam) +
            (1 - phiStar lam c Rbar t) * (3 / 4 * (Rbar - c / lam))) := by sorry

end DevContest
