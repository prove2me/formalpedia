-- Prove2me | Theorems.Thm_BernoulliQPTAS_Scheduling_lemma_4_2
-- name    : BernoulliQPTAS.Scheduling.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:48.622992+00:00
-- url     : https://prove2.me/theorems/c174634d-303c-444e-81f7-94539b8c38f1
-- title:
--   Lemma 4.2 — stretching and compression
-- statement:
--   Fix $K\ge1$ and $\gamma=1+1/K$. Let $\Pi^*$ be a deterministic non-idling optimal policy respecting the class orders. There exists a grid-non-idling reuse-rule policy $\Pi$ respecting those orders such that, on the same complete outcome vector $\omega$,
--
--   $$S_j^\Pi(\omega)\le\gamma S_j^{\Pi^*}(\omega)\quad\text{for every job }j\text{ and every realization }\omega,$$
--
--   and
--
--   $$\operatorname{cost}(\Pi)\le P+\gamma(\operatorname{OPT}-P).$$
--
--   Both the realizationwise coupling and the expected-cost conclusion are retained. The fixed comparator has exactly the properties supplied by Lemma 2.4.
--
--   Differences from the source:
--   - encoding: finite labeled jobs and machines with nonnegative real scheduling times → Fin N and Fin m labels with nonnegative real times and extended nonnegative expected costs; reason: the same instances, schedules, and expectations, including infinite expected costs, are represented
-- source:
--   Junho Hwang, STOC 2027 submission #427 (October 2026), Lemma 4.2, p. 11; canonical PDF SHA256 5d2e3fc3a3b47830c7018375aacf3e77df7f0e30725fecb62845334a8f0be7a9

import Definitions.Def_BernoulliQPTAS_Scheduling_ReleaseDP

open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace BernoulliQPTAS.Scheduling

theorem lemma_4_2 {N m : ℕ} (I : Instance N m) (hm : 0 < m) (hmN : m < N)
    (K : ℕ) (hK : 1 ≤ K) (star : PolicyTree N m)
    (hvalid : Admissible I (initialState Finset.univ) star)
    (hnoidle : NonIdling I (initialState Finset.univ) star)
    (hclass : RespectsClasses I (initialState Finset.univ) star)
    (hopt : treeCost I star = optimum I (initialState Finset.univ)) :
    ∃ t : PolicyTree N m,
      ReuseAdmissible I K (initialState Finset.univ) t ∧
      GridNonIdling I K (initialState Finset.univ) t ∧
      RespectsClasses I (initialState Finset.univ) t ∧
      (∀ j ω, (startTime t ω j : ℝ) ≤ (1 + 1 / (K : ℝ)) * startTime star ω j) ∧
      treeCost I t ≤ totalMean I Finset.univ +
        ENNReal.ofReal (1 + 1 / (K : ℝ)) *
          (optimum I (initialState Finset.univ) - totalMean I Finset.univ) := by sorry

end BernoulliQPTAS.Scheduling
