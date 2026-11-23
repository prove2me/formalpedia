-- Prove2me | Theorems.Thm_BestBothWorlds_SAO_Supplement_two_arm_existence
-- name    : BestBothWorlds.SAO.Supplement.two_arm_existence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:17:36.52481+00:00
-- url     : https://prove2.me/theorems/86907548-6f10-4951-a7db-fd2c236df7aa
-- title:
--   Theorem 3.1 — One two-arm algorithm for both reward models
-- statement:
--   There is one horizon-aware two-arm bandit algorithm and positive absolute constants $A,B$ such that, for every $n\ge2$, against every oblivious reward sequence in $[0,1]^2$ its expected regret is at most $A\sqrt n\log^2 n$, and its regret is at most that bound with probability at least $1-1/n$. For every stochastic two-arm instance of positive gap $\Delta=|\mu_1-\mu_2|$, its expected pseudo-regret is at most $B\log^3(n)/\Delta$, and its pseudo-regret is at most that bound with probability at least $1-1/n$.
--
--   $$\mathbb E[R_n]\le A\sqrt n\log^2 n,\qquad
--   \mathbb E[\overline R_n]\le B\log^3(n)/\Delta.$$
--
--   At equal means the pseudo-regret is zero with probability one and in expectation. The same algorithm serves every instance and both models. The algorithm and constants are chosen before the horizon and rewards, so neither can adapt to an unknown instance.
--
--   This is the existential theorem on p. 5, a companion to the published goal. The source's unspecified exploration cutoff in the simplified §3.1 algorithm does not obstruct stating existence of a bandit algorithm.
--
--   **Formalization Note** An algorithm is a family, indexed by the horizon $n$, of maps from the observed history to a probability vector on the two arms (nonnegative entries summing to one), whose path probabilities are measurable in the reward table so that the stochastic expectations and probabilities are genuine. The witness is not fixed: neither the simplified algorithm of §3.1 nor SAO is named in the statement. A fixed reward table encodes any oblivious adversary. Expectations and probabilities use the published interaction law.
--
--   Differences from the source:
--   - encoding: Existence of a two-arm algorithm and O(·) bounds in expectation and with probability 1−1/n → A horizon-indexed family of Policy 2 maps, each returning a probability vector with measurable path probabilities, followed by positive absolute constants A,B, and all n≥2 and instances; reason: A randomized algorithm samples from a distribution and knows n; the same family serves every instance, and O(·) constants are uniform
--   - generalization: Stochastic logarithmic bound with inverse gap → Positive-gap bounds plus exactly zero pseudo-regret in expectation and with probability one when Δ=0; reason: No source instance with positive gap is removed, and equal means make every pseudo-regret summand zero
-- source:
--   Bubeck & Slivkins, The best of both worlds: stochastic and adversarial bandits, arXiv:1202.4473v1, p. 5, Theorem 3.1

import Mathlib
import Definitions.Def_BestBothWorlds_SAO_Interaction

open MeasureTheory

namespace BestBothWorlds.SAO.Supplement

/-- Theorem 3.1, p. 5: one horizon-aware algorithm works in both models,
in expectation and with probability at least `1 - 1/n`.
The theorem asserts existence of a randomized algorithm: a family, indexed by the horizon
`n`, of maps from the observed history to a probability vector on the two arms (nonnegative
entries summing to one), whose path probabilities are measurable functions of the reward
table, so that the stochastic expectations and probabilities are genuine. The witness is not fixed to the simplified algorithm of §3.1.
A deterministic reward table is an arbitrary oblivious adversary. Both constants are
absolute. At equal stochastic means the pseudo-regret is identically zero; the gap quotient
is only used at positive gap. -/
theorem two_arm_existence :
    ∃ π : ℕ → Policy 2,
      (∀ n (h : History 2), (∀ i, 0 ≤ π n h i) ∧ ∑ i, π n h i = 1) ∧
      (∀ n (I : Fin n → Fin 2),
        Measurable (fun ω : Fin n → Fin 2 → ℝ => pathProb (π n) (tableAdv ω) I)) ∧
      ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ n : ℕ, 2 ≤ n →
        (∀ g : Fin n → Fin 2 → ℝ,
          (∀ t i, g t i ∈ Set.Icc (0 : ℝ) 1) →
          let b : ℝ := A * Real.sqrt (n : ℝ) * Real.log (n : ℝ) ^ 2
          (∑ I : Fin n → Fin 2, pathProb (π n) (tableAdv g) I *
            regret (tableAdv g) I) ≤ b ∧
          1 - 1 / (n : ℝ) ≤ probEvent n (π n) (tableAdv g)
            (fun I => regret (tableAdv g) I ≤ b)) ∧
        (∀ (ν : Fin 2 → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)],
          (∀ i, ν i (Set.Icc 0 1)ᶜ = 0) →
          let Δ : ℝ := |mean ν 0 - mean ν 1|
          let E : ℝ := ∫ ω,
            (∑ I : Fin n → Fin 2, pathProb (π n) (tableAdv ω) I *
              pseudoRegret (mean ν) I) ∂(rewardTableMeasure n ν)
          (0 < Δ →
            let b : ℝ := B / Δ * Real.log (n : ℝ) ^ 3
            E ≤ b ∧
            1 - 1 / (n : ℝ) ≤ probStoch n (π n) ν
              (fun _ I => pseudoRegret (mean ν) I ≤ b)) ∧
          (Δ = 0 → E = 0 ∧
            1 ≤ probStoch n (π n) ν (fun _ I => pseudoRegret (mean ν) I = 0))) := by sorry

end BestBothWorlds.SAO.Supplement
