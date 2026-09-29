-- Prove2me | Theorems.Thm_BanditAlgorithm_bayesian_ts_conditional_gains_accounting
-- name    : BanditAlgorithm.bayesian_ts_conditional_gains_accounting
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-02T01:39:44.4007+00:00
-- url     : https://prove2.me/theorems/0eefc8b6-41c2-4711-a4b7-965e3760077b
-- title:
--   One-round conditional gain accounting
-- statement:
--   Fix a round $t$ and let $\nu_t$ be the law of the history before that round. The average conditional regret equals the unconditional expected one-round regret,
--
--   $$
--   \mathbb E[X_{t,A^*}-X_{t,A_t}]=\int r_t(h)\,\nu_t(dh).
--   $$
--
--   The average conditional information gain is at most the corresponding increment of mutual information,
--
--   $$
--   \int g_t(h)\,\nu_t(dh)\le I(A^*;H_{t+1})-I(A^*;H_t).
--   $$
--
--   This statement supplies the disintegration and information-accounting interface needed to sum the one-round information-ratio bounds.
--
--   **Formalization Note** Histories are terminal-law prefix maps, and mutual information is represented as Kullback--Leibler divergence from the product of marginals.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), Lemma 36.7, printed p. 470 (free PDF p. 479), https://tor-lattimore.com/downloads/book/book.pdf; conditional-law and Bayes/chain-rule formalization.

import Definitions.Def_BayesianTSRoundConditionalGains
import Mathlib.InformationTheory.KullbackLeibler.ChainRule

open MeasureTheory ProbabilityTheory InformationTheory

namespace BanditAlgorithm

/-- Disintegration and KL-chain-rule accounting for the conditional regret
and information gains in one Thompson-sampling round. -/
theorem bayesian_ts_conditional_gains_accounting
    {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ X ∂Q, ∀ (s : Fin n) (a : Fin k), X s a ∈ Set.Icc (0 : ℝ) 1)
    {pi : BanditPolicy k} (t : Fin n) :
    let history := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
      fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)
    let nu := Measure.map history (bayesianAdversarialMeasure Q pi n le_rfl)
    (∫ p, (p.1 t (bayesianOptimalAction p.1) - p.1 t ((p.2 t).1))
        ∂bayesianAdversarialMeasure Q pi n le_rfl) =
      ∫ h, bayesianTSRoundConditionalRegretGain Q pi t h ∂nu ∧
    (∫ h, bayesianTSRoundConditionalInformationGain Q pi t h ∂nu) ≤
      bayesianHistoryMutualInformation Q pi (t.1 + 1) (Nat.succ_le_iff.mpr t.2) -
        bayesianHistoryMutualInformation Q pi t.1 (Nat.le_of_lt t.2) := by
  sorry

end BanditAlgorithm
