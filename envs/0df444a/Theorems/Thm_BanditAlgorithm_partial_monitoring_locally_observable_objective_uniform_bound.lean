-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_locally_observable_objective_uniform_bound
-- name    : BanditAlgorithm.partial_monitoring_locally_observable_objective_uniform_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T17:36:56.642692+00:00
-- url     : https://prove2.me/theorems/bf591193-60b7-449e-9bfe-733ee974cd38
-- title:
--   Uniform Algorithm 26 objective bound for locally observable games
-- statement:
--   Let G be a locally observable finite partial-monitoring game with k at least two, a nonempty outcome set, and losses in [0,1]. There exist a nonempty finite comparator set S, a nonnegative constant A, and a threshold eta_0>0 such that S contains a hindsight-optimal action for every finite outcome sequence. For every learning rate 0<eta<=eta_0 and every probability distribution q supported on S, there are an interior sampling distribution p and a vector loss estimator f satisfying
--
--   $$
--   \max_i \operatorname{Obj}_{G,\eta}(q,p,f;i) \leq A.
--   $$
--
--   Here the objective is the exploration--stability quantity in equation (37.12). This is the horizon-free geometric core of the locally observable upper bound; choosing eta as a function of the horizon is a separate elementary step.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Chapter 37, Theorem 37.17 and its proof in Sections 37.7--37.7.1, printed pp. 498--502, especially equations (37.16)--(37.17), https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringAlgorithm26

open scoped BigOperators

namespace BanditAlgorithm

/-! Lattimore--Szepesvári, Theorem 37.17, printed pp. 498--502, before
the horizon-dependent tuning of the learning rate. -/

theorem partial_monitoring_locally_observable_objective_uniform_bound
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (hk : 2 ≤ k)
    (hd : 0 < d)
    (hL : ∀ a i, G.L a i ∈ Set.Icc (0 : ℝ) 1)
    (hloc : LocallyObservable G) :
    ∃ S : Finset (Fin k), ∃ A η₀ : ℝ,
      S.Nonempty ∧ 0 ≤ A ∧ 0 < η₀ ∧
      (∀ (n : ℕ) (i : Fin n → Fin d), ∃ b ∈ S, ∀ a : Fin k,
        ∑ t, G.L b (i t) ≤ ∑ t, G.L a (i t)) ∧
      ∀ η : ℝ, 0 < η → η ≤ η₀ →
        ∀ q : Fin k → ℝ, PMSupportedOn S q →
          ∃ p : Fin k → ℝ, ∃ f : Fin k → 𝕊 → Fin k → ℝ,
            PMInteriorDistribution p ∧ PMVectorEstimatorOn G S f ∧
            ∀ i : Fin d, pmAlgorithm26Objective G η q p f i ≤ A := by
  sorry

end BanditAlgorithm
