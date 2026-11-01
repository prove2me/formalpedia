-- Prove2me | Theorems.Thm_DevContest_first_success_time
-- name    : DevContest.first_success_time
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:53:10.631539+00:00
-- url     : https://prove2.me/theorems/1d03b6c6-ec08-46e9-8231-ecf7f8849d38
-- title:
--   Proof of Theorem 2, p.ec18 — PCSD minimizes the expected time until the first success
-- statement:
--   Let $\lambda,c>0$ and $2c/\lambda<\bar R<3c/\lambda$. For every disclosure policy and every admissible profile, the expected date of the first success of the contest is at least $1/(2\lambda)$. Under PCSD with its equilibrium strategies it equals $1/(2\lambda)$.
--
--   This is the first of the two parts into which the proof of Theorem 2 splits the expected lead time. Here $1/(2\lambda)$ is the first term in the display (EC.1).
--
--   Differences from the source:
--   - generalization: PCSD minimizes that time among contests → the bound holds for every admissible profile of every policy, not only for equilibria; reason: equilibria are admissible profiles
--   - encoding: a stage succeeds at a Poisson arrival with instantaneous probability $\lambda x$ → a stage ends when $\int\lambda x$ reaches an independent unit-exponential clock; reason: this is the standard time change of the same point process; it has the same law for every effort path
-- source:
--   Khorasani, Körpeoğlu, Krishnan, Dynamic Development Contests, author manuscript, p.ec18; display (EC.1), p.ec1

import Mathlib
import Definitions.Def_DevContest_payoff
import Definitions.Def_DevContest_pcsd

open scoped ENNReal NNReal

namespace DevContest

/-- Khorasani, Körpeoğlu, Krishnan, *Dynamic Development Contests*, author manuscript, p.ec18: PCSD
minimizes the expected time until the first success, because both agents exert full effort until
it arrives. For every policy and every admissible profile that time is at least `1/(2λ)`, the first
term of (EC.1), p.ec1, and PCSD with its equilibrium strategies attains it. -/
theorem first_success_time {lam c Rbar : ℝ} (hlam : 0 < lam) (hc : 0 < c)
    (hlow : 2 * c / lam < Rbar) (hhigh : Rbar < 3 * c / lam) :
    (∀ (U M : Type) [MeasurableSpace U] (D : Policy U M) (x : Fin 2 → Strategy U),
      (∀ i, IsAdmissible D i (x i)) →
      ENNReal.ofReal (1 / (2 * lam)) ≤
        ∫⁻ ω : U × Clocks, min ((play lam x ω.1 ω.2).first 0) ((play lam x ω.1 ω.2).first 1)
          ∂(law D)) ∧
    ∫⁻ ω : unitInterval × Clocks,
      min ((play lam (pcsdEffort lam c Rbar) ω.1 ω.2).first 0)
        ((play lam (pcsdEffort lam c Rbar) ω.1 ω.2).first 1) ∂(law (pcsd lam c Rbar)) =
      ENNReal.ofReal (1 / (2 * lam)) := by sorry

end DevContest
