-- Prove2me | Theorems.Thm_BanditAlgorithm_etc_commit_arm_probability_bound
-- name    : BanditAlgorithm.etc_commit_arm_probability_bound
-- status  : Proved
-- author  : @ann
-- created : 2026-07-22T15:11:56.803181+00:00
-- url     : https://prove2.me/theorems/f049f4c5-500d-4673-adce-bdf23848f99a
-- title:
--   ETC commit-arm probability bound (Eq. 6.3)
-- statement:
--   Let $k>0$, let $m\ge 1$, and run Explore-Then-Commit on a 1-subgaussian $k$-armed bandit. Let $C$ be the empirical-mean maximizer selected after the deterministic round-robin exploration phase. At every post-exploration horizon $r\ge mk$, the policy selects $C$, and for every arm $i$,
--
--   $$
--   \mathbb P(C=i) \le \exp\!\left(-\frac{m\Delta_i^2}{4}\right).
--   $$
--
--   The indicator of the commit event is integrable under the canonical history law, and the same probability bound holds after pulling that event back from any later history to its exploration prefix. The statement includes optimal arms ($\Delta_i=0$), where the bound remains valid.
--
--   This is the reusable concentration half of the ETC analysis: it isolates exactly the wrong-commit estimate used in the one-step occupation recursion.
--
--   **Formalization Note** The witness $C$ also carries the empirical-maximizer property and the deterministic post-exploration selection identity required by the canonical bandit-measure calculation.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), Section 6.1, Theorem 6.1, printed pp. 92--93 / PDF pp. 101--102, Algorithm 1 and Eq. (6.3).

import Definitions.Def_etcPolicy

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.etc_commit_arm_probability_bound
    {k : ℕ} (hk : 0 < k)
    {ν : BanditAlgorithm.StochasticBandit k}
    (hν : BanditAlgorithm.IsSubgaussianBandit 1 ν)
    {m : ℕ} (hm : 1 ≤ m) {π : BanditAlgorithm.BanditPolicy k}
    (hπ : BanditAlgorithm.IsETCPolicy hk m π)
    (i : Fin k) :
    ∃ commit : BanditAlgorithm.BanditHistory k (m * k) → Fin k,
      (∀ h₀ : BanditAlgorithm.BanditHistory k (m * k), ∀ j : Fin k,
        BanditAlgorithm.armEmpiricalMean j h₀ ≤
          BanditAlgorithm.armEmpiricalMean (commit h₀) h₀) ∧
      (∀ (r : ℕ) (h : BanditAlgorithm.BanditHistory k r)
          (hr : m * k ≤ r),
        (π.select r) h =
          Measure.dirac (commit (BanditAlgorithm.banditExplorationPrefix
            hr h))) ∧
      ∀ (r : ℕ) (hr : m * k ≤ r),
        Integrable
          (fun h : BanditAlgorithm.BanditHistory k r ↦
            if commit (BanditAlgorithm.banditExplorationPrefix hr h) = i
            then (1 : ℝ) else 0)
          (BanditAlgorithm.banditMeasure ν π r) ∧
        ∫ h, (if commit (BanditAlgorithm.banditExplorationPrefix hr h) = i
            then (1 : ℝ) else 0)
            ∂BanditAlgorithm.banditMeasure ν π r ≤
          Real.exp (-(m * (BanditAlgorithm.banditGap ν i) ^ 2) / 4) := by
  sorry
