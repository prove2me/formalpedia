-- Prove2me | Theorems.Thm_BanditAlgorithm_bayesian_ts_conditional_regret_gain_integral
-- name    : BanditAlgorithm.bayesian_ts_conditional_regret_gain_integral
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-02T01:48:26.05977+00:00
-- url     : https://prove2.me/theorems/71bbda63-bd84-40ac-a393-e97c0e02c9cc
-- title:
--   Tower property for conditional Thompson regret
-- statement:
--   Fix a round $t$ and let $\nu_t$ be the law of the history before that round. If $r_t(h)$ denotes the conditional expected one-round regret, then
--
--   $$
--   \mathbb E[X_{t,A^*}-X_{t,A_t}]=\int r_t(h)\,\nu_t(dh).
--   $$
--
--   This is the tower-property component of the one-round Bayesian regret decomposition.
--
--   **Formalization Note** The bounded-reward hypothesis ensures integrability, and the terminal interconnection law is disintegrated over its pre-round history prefix.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), Lemma 36.7, printed p. 470 (free PDF p. 479), https://tor-lattimore.com/downloads/book/book.pdf; conditional-law and Bayes/chain-rule formalization.

import Definitions.Def_BayesianTSRoundConditionalGains

open MeasureTheory ProbabilityTheory InformationTheory

namespace BanditAlgorithm

/-- Tower-property accounting for the conditional one-round regret gain. -/
theorem bayesian_ts_conditional_regret_gain_integral
    {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ X ∂Q, ∀ (s : Fin n) (a : Fin k), X s a ∈ Set.Icc (0 : ℝ) 1)
    {pi : BanditPolicy k} (t : Fin n) :
    let history := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
      fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)
    let nu := Measure.map history (bayesianAdversarialMeasure Q pi n le_rfl)
    (∫ p, (p.1 t (bayesianOptimalAction p.1) - p.1 t ((p.2 t).1))
        ∂bayesianAdversarialMeasure Q pi n le_rfl) =
      ∫ h, bayesianTSRoundConditionalRegretGain Q pi t h ∂nu := by
  sorry

end BanditAlgorithm
