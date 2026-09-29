-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_stopped_bretagnolle_huber
-- name    : BanditAlgorithm.bandit_stopped_bretagnolle_huber
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T19:29:33.246452+00:00
-- url     : https://prove2.me/theorems/d6992c63-cdd3-42d4-ad33-15832244838c
-- title:
--   Bretagnolle--Huber inequality at an adaptive bandit stopping time
-- statement:
--   Run a common adaptive policy in two bandit environments $\nu$ and $\nu'$, and observe the experiment only until an integrable stopping time $\tau$. For every event $A$ measurable from the stopped experiment, let
--
--   $$
--   I_\tau=\sum_{i=1}^k \mathbb E_{\nu,\pi}[T_i(\tau)]D(\nu_i\Vert\nu_i').
--   $$
--
--   When $I_\tau<\infty$, the two testing errors satisfy the stopped Bretagnolle--Huber inequality
--
--   $$
--   \frac12 e^{-I_\tau}
--   \le
--   \mathbb P_{\nu,\pi}(A^c)+\mathbb P_{\nu',\pi}(A).
--   $$
--
--   This is the stopping-time extension of the canonical bandit divergence decomposition followed by data processing to the binary decision $A$.
-- source:
--   Lattimore--Szepesvári, Bandit Algorithms (CUP 2020), Exercise 15.7, printed p. 211 (stopping-time extension of Lemma 15.1), combined with Theorem 14.2, printed pp. 190--191 (Bretagnolle--Huber).

import Definitions.Def_BanditTrajectory

open MeasureTheory ProbabilityTheory InformationTheory ENNReal

theorem BanditAlgorithm.bandit_stopped_bretagnolle_huber
    {k : ℕ} (ν ν' : StochasticBandit k) (π : BanditPolicy k)
    (τ : (ℕ → Fin k × ℝ) → ℕ∞) (hτ : IsBanditStoppingTime τ)
    (hfinite : ∫⁻ ω, (τ ω : ℝ≥0∞) ∂banditTrajMeasure ν π < ⊤)
    (A : Set (ℕ → Fin k × ℝ)) (hA : Measurable[hτ.measurableSpace] A)
    (hinfo : (∑ i, (∫⁻ ω, ∑' t : ℕ,
          if (t : ℕ∞) < τ ω ∧ (ω t).1 = i then (1 : ℝ≥0∞) else 0
        ∂banditTrajMeasure ν π) * klDiv (ν.P i) (ν'.P i)) ≠ ⊤) :
    (2 : ℝ)⁻¹ * Real.exp
        (-(∑ i, (∫⁻ ω, ∑' t : ℕ,
            if (t : ℕ∞) < τ ω ∧ (ω t).1 = i then (1 : ℝ≥0∞) else 0
          ∂banditTrajMeasure ν π) * klDiv (ν.P i) (ν'.P i)).toReal) ≤
      (banditTrajMeasure ν π).real Aᶜ +
        (banditTrajMeasure ν' π).real A := by
  sorry
