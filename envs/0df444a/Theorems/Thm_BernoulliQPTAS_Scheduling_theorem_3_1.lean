-- Prove2me | Theorems.Thm_BernoulliQPTAS_Scheduling_theorem_3_1
-- name    : BernoulliQPTAS.Scheduling.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:09.114162+00:00
-- url     : https://prove2.me/theorems/94217707-b891-43ae-940c-78e70d3fe0c2
-- title:
--   Theorem 3.1 — approximation-preserving size reduction
-- statement:
--   Let $2\le m<N$, $0<\varepsilon\le1$, and $\alpha\ge1$. Partition the jobs at thresholds $T=NP/\varepsilon$ and $\sigma=\varepsilon P/N^2$ as in the wrapper definition, and let $M$ be the medium-job set. For every admissible randomized policy $A$ for $M$ satisfying $\operatorname{cost}(A)\le\alpha\operatorname{OPT}(M)$, its specified large/small/medium wrapper $\Pi_A$ is an admissible randomized policy and
--
--   $$\operatorname{cost}(\Pi_A)\le(\alpha+2\varepsilon)\operatorname{OPT}.$$
--
--   The conclusion includes that the pushforward law of the wrapper has total mass one and is almost surely physically admissible. The empty-medium case is included. This preserves the approximation ratio up to exactly the source's additive $2\varepsilon$.
--
--   The list-scheduling order is an arbitrary fixed list of all jobs, as on p.9.
--
--   Differences from the source:
--   - encoding: finite labeled jobs and machines with nonnegative real scheduling times → Fin N and Fin m labels with nonnegative real times and extended nonnegative expected costs; reason: the same instances, schedules, and expectations, including infinite expected costs, are represented
-- source:
--   Junho Hwang, STOC 2027 submission #427 (October 2026), Theorem 3.1, p. 10; canonical PDF SHA256 5d2e3fc3a3b47830c7018375aacf3e77df7f0e30725fecb62845334a8f0be7a9

import Definitions.Def_BernoulliQPTAS_Scheduling_Reduction

open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace BernoulliQPTAS.Scheduling

theorem theorem_3_1 {N m : ℕ} (I : Instance N m) (hm : 2 ≤ m) (hmN : m < N)
    (ε α : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hα : 1 ≤ α)
    (order : List (Fin N)) (horder : order.Perm (List.finRange N))
    (A : RandomPolicy N m)
    (hvalid : RandomAdmissible I (initialState (mediumJobs I ε)) A)
    (happrox : randomCost I A ≤ ENNReal.ofReal α * optimum I (initialState (mediumJobs I ε))) :
    MeasureTheory.IsProbabilityMeasure (wrapperLaw I ε order A) ∧
      (∀ᵐ t ∂(wrapperLaw I ε order A), Admissible I (initialState Finset.univ) t) ∧
      wrapperCost I ε order A ≤ ENNReal.ofReal (α + 2 * ε) *
        optimum I (initialState Finset.univ) := by sorry

end BernoulliQPTAS.Scheduling
