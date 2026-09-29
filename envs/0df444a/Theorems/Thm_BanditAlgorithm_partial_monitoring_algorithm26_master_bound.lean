-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_algorithm26_master_bound
-- name    : BanditAlgorithm.partial_monitoring_algorithm26_master_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T17:26:42.504003+00:00
-- url     : https://prove2.me/theorems/ffd1fdf4-c048-4e6d-b904-adc7461554df
-- title:
--   Algorithm 26 master regret bound
-- statement:
--   Let G be a finite partial-monitoring game, let S be a nonempty finite comparator set containing an optimal action for every finite outcome sequence, and let eta be positive. Suppose that for every exponential-weights distribution q supported on S, one can choose an interior action distribution p and a vector loss estimator f whose Algorithm 26 exploration--stability objective is at most B for every outcome. If the outcome set is nonempty, then for every horizon n there exists a partial-monitoring policy pi satisfying
--
--   $$
--   \sup_{i_{1:n}} R_n(\pi,i_{1:n}) \leq \frac{\log |S|}{\eta}+n\eta B.
--   $$
--
--   This is the master online-learning reduction behind Algorithm 26: any uniform one-step bound on its optimization objective yields a finite-horizon worst-case regret guarantee.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Chapter 37, Theorem 37.15 and equations (37.11)--(37.15), printed pp. 493--495, https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringAlgorithm26

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BanditAlgorithm
theorem partial_monitoring_algorithm26_master_bound
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    [MeasurableSingletonClass 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (S : Finset (Fin k))
    (hS : S.Nonempty) (η B : ℝ) (hη : 0 < η) (hd : 0 < d)
    (hbest : ∀ (n : ℕ) (i : Fin n → Fin d), ∃ b ∈ S, ∀ a : Fin k,
      ∑ t, G.L b (i t) ≤ ∑ t, G.L a (i t))
    (hsolve : ∀ q : Fin k → ℝ, PMSupportedOn S q →
      ∃ p : Fin k → ℝ, ∃ f : Fin k → 𝕊 → Fin k → ℝ,
        PMInteriorDistribution p ∧ PMVectorEstimatorOn G S f ∧
        ∀ i : Fin d, pmAlgorithm26Objective G η q p f i ≤ B) :
    ∀ n : ℕ, ∃ π : PMPolicy k 𝕊,
      (⨆ i : Fin n → Fin d, pmRegret G π n i) ≤
        Real.log S.card / η + (n : ℝ) * η * B := by
  sorry

end BanditAlgorithm
