-- Prove2me | Theorems.Thm_BanditAlgorithm_bayesianAdversarialMeasure_prefix_marginal
-- name    : BanditAlgorithm.bayesianAdversarialMeasure_prefix_marginal
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-02T00:47:00.362838+00:00
-- url     : https://prove2.me/theorems/1ecde00c-c5e5-420b-9ecc-ba4da8b5b5b9
-- title:
--   Prefix consistency of the Bayesian adversarial-bandit law
-- statement:
--   For the Bayesian adversarial-bandit interconnection, the law constructed through any horizon $u$ has the recursively constructed law through every earlier time $t\le u$ as its prefix marginal. Concretely, if one keeps the sampled reward matrix and truncates the length-$u$ history to its first $t$ observations, the resulting pushforward measure is exactly the joint law of the reward matrix and the length-$t$ history.
--
--   $$
--   (X,H_u)\mapsto(X,H_t)
--   \quad\Longrightarrow\quad
--   \mathcal L(X,H_t)=B_{Q,\pi}^{,t}.
--   $$
--
--   This projective-consistency result is the structural bridge that permits one-round conditional calculations to be performed under the recursively defined prefix law while the mutual-information definition uses the terminal law.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), §36.4, printed pp. 469–470 (free PDF pp. 478–479), https://tor-lattimore.com/downloads/book/book.pdf; purely formal projective-consistency bridge for the recursively defined interconnection law.

import Definitions.Def_ThompsonSampling

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-- The terminal interconnection law has the recursively constructed shorter law as every prefix. -/
theorem bayesianAdversarialMeasure_prefix_marginal {k n : ℕ}
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (pi : BanditPolicy k) (u : ℕ) (hu : u ≤ n) (t : ℕ) (ht : t ≤ u) :
    Measure.map
        (fun p : (Fin n → Fin k → ℝ) × BanditHistory k u ↦
          (p.1, fun s : Fin t ↦ p.2 (Fin.castLE ht s)))
        (bayesianAdversarialMeasure Q pi u hu) =
      bayesianAdversarialMeasure Q pi t (ht.trans hu) := by
  sorry

end BanditAlgorithm
