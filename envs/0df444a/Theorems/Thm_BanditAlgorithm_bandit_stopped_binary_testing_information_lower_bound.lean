-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_stopped_binary_testing_information_lower_bound
-- name    : BanditAlgorithm.bandit_stopped_binary_testing_information_lower_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T19:21:21.791578+00:00
-- url     : https://prove2.me/theorems/40ef213c-3aa3-4b8e-8827-84c2722c99dc
-- title:
--   Stopped binary-testing information inequality for adaptive bandits
-- statement:
--   Run the same adaptive bandit policy $\pi$ in two environments $\nu$ and $\nu'$, and stop at an almost surely integrable stopping time $\tau$. Let $A$ be any event measurable from the stopped experiment. If the two testing errors satisfy
--
--   $$
--   \mathbb P_{\nu,\pi}(A^c)\le\delta,
--   \qquad
--   \mathbb P_{\nu',\pi}(A)\le\delta,
--   $$
--
--   then the expected information collected before stopping obeys
--
--   $$
--   \log\!\frac{1}{4\delta}
--   \le
--   \sum_{i=1}^k \mathbb E_{\nu,\pi}[T_i(\tau)]
--   D(\nu_i\Vert\nu_i').
--   $$
--
--   Here $T_i(\tau)=\sum_{t\ge0}\mathbf 1\{t<\tau, A_t=i\}$. This is the stopping-time form of the canonical bandit divergence decomposition combined with the Bretagnolle--Huber binary-testing inequality.
-- source:
--   Lattimore--Szepesvári, Bandit Algorithms (CUP 2020), Exercise 15.7, printed p. 211 (stopping-time extension of Lemma 15.1), combined with Theorem 14.2, printed pp. 190--191 (Bretagnolle--Huber); used in Theorem 33.5, Eq. (33.6), printed p. 407.

import Definitions.Def_BanditTrajectory

open MeasureTheory ProbabilityTheory InformationTheory ENNReal

theorem BanditAlgorithm.bandit_stopped_binary_testing_information_lower_bound
    {k : ℕ} (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (ν ν' : StochasticBandit k) (π : BanditPolicy k)
    (τ : (ℕ → Fin k × ℝ) → ℕ∞) (hτ : IsBanditStoppingTime τ)
    (hfinite : ∫⁻ ω, (τ ω : ℝ≥0∞) ∂banditTrajMeasure ν π < ⊤)
    (A : Set (ℕ → Fin k × ℝ)) (hA : Measurable[hτ.measurableSpace] A)
    (hνerr : (banditTrajMeasure ν π).real Aᶜ ≤ δ)
    (hν'err : (banditTrajMeasure ν' π).real A ≤ δ) :
    ENNReal.ofReal (Real.log (1 / (4 * δ))) ≤
      ∑ i, (∫⁻ ω, ∑' t : ℕ,
          if (t : ℕ∞) < τ ω ∧ (ω t).1 = i then (1 : ℝ≥0∞) else 0
        ∂banditTrajMeasure ν π) * klDiv (ν.P i) (ν'.P i) := by
  sorry
