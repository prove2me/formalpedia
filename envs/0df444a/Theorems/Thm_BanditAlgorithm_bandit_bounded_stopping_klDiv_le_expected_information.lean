-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_bounded_stopping_klDiv_le_expected_information
-- name    : BanditAlgorithm.bandit_bounded_stopping_klDiv_le_expected_information
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T19:49:11.621822+00:00
-- url     : https://prove2.me/theorems/e6c6a17b-7776-42cf-b001-389ed3828f0b
-- title:
--   Finite-horizon KL chain rule at a bounded bandit stopping time
-- statement:
--   Run an adaptive policy $\pi$ in two $k$-armed environments $\nu$ and $\nu'$. Let $\tau$ be a stopping time and fix a deterministic horizon $n$. For the bounded stopping time $\tau_n=\min\{\tau,n\}$, the relative entropy between the two experiments observed through $\mathcal F_{\tau_n}$ is at most the expected armwise information gathered before $\tau_n$:
--
--   $$
--   D\!\left(\mathbb P_{\nu,\pi}|_{\mathcal F_{\tau_n}}\,\middle\Vert\,
--             \mathbb P_{\nu',\pi}|_{\mathcal F_{\tau_n}}\right)
--   \le
--   \sum_{i=1}^k \mathbb E_{\nu,\pi}[T_i(\tau_n)]
--          D(\nu_i\Vert\nu_i').
--   $$
--
--   This is the bounded stopping-time form of the adaptive divergence decomposition. It isolates the finite likelihood-chain calculation from the separate limiting argument needed for unbounded stopping times.
--
--   **Formalization Note** Pulls are numbered from zero in the canonical trajectory, so $T_i(\tau_n)$ counts indices $t$ satisfying $t<\min(\tau,n)$ and $A_t=i$.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Lemma 15.1, Eq. (15.1), printed p. 198, together with Exercise 15.7, printed p. 211, bounded-stopping-time step.

import Definitions.Def_BanditTrajectory

open MeasureTheory ProbabilityTheory InformationTheory ENNReal

theorem BanditAlgorithm.bandit_bounded_stopping_klDiv_le_expected_information
    {k : ℕ} (ν ν' : StochasticBandit k) (π : BanditPolicy k)
    (τ : (ℕ → Fin k × ℝ) → ℕ∞) (hτ : IsBanditStoppingTime τ) (n : ℕ) :
    @klDiv (ℕ → Fin k × ℝ) (hτ.min_const n).measurableSpace
        ((banditTrajMeasure ν π).trim (hτ.min_const n).measurableSpace_le)
        ((banditTrajMeasure ν' π).trim (hτ.min_const n).measurableSpace_le) ≤
      ∑ i, (∫⁻ ω, ∑' t : ℕ,
          if (t : ℕ∞) < min (τ ω) n ∧ (ω t).1 = i
            then (1 : ℝ≥0∞) else 0
        ∂banditTrajMeasure ν π) * klDiv (ν.P i) (ν'.P i) := by
  sorry
