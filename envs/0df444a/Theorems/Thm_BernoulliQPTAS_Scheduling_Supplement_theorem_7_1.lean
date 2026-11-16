-- Prove2me | Theorems.Thm_BernoulliQPTAS_Scheduling_Supplement_theorem_7_1
-- name    : BernoulliQPTAS.Scheduling.Supplement.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:39:57.721635+00:00
-- url     : https://prove2.me/theorems/19d133fb-e901-44ad-b768-dd16394dd31d
-- title:
--   Theorem 7.1 — every list policy loses a factor $b/768\ge\log_2N/1536$
-- statement:
--   For every integer $b\ge2$, let $M=2^b$ and consider two machines with $M$ jobs of each type $i=0,\dots,b-1$, where a job of type $i$ has
--
--   $$
--   p_i=\frac{M^2}{4^i},\qquad q_i=\frac{2^i}{M^2},
--   $$
--
--   and let $N=bM$. A list policy fixes, for each value of its coins, an order of the jobs before any outcome is observed and starts the jobs in this order. Its start times are otherwise free, so it may idle. Then:
--
--   1. every admissible list policy $\Pi$ has $\mathrm{cost}(\Pi)\ge Mb^2/128$;
--   2. $\mathrm{OPT}\le 6Mb$;
--   3. hence every admissible list policy satisfies $\mathrm{cost}(\Pi)\ge\frac{b}{768}\,\mathrm{OPT}$, and $\frac{b}{768}\ge\frac{\log_2N}{1536}$.
--
--   Thus every list policy has ratio $\Omega(\log N)$, even on two machines (Theorem 1.5), and the $O(\log^2N)$ bound of Im, Moseley and Pruhs for two machines is tight up to a factor $O(\log N)$.
--
--   **Formalization Note** A list policy is a randomized policy for which, for almost every value of its coins, the realized sequence of started jobs is the same list on every outcome. $\mathrm{OPT}$ is the published optimum over all adaptive, randomized and idling policies.
--
--   Differences from the source:
--   - encoding: "every list policy has ratio at least b/768" → cost(Π) ≥ (b/768)·OPT for every admissible list policy Π; reason: the ratio is cost/OPT, and OPT is positive and finite
--   - encoding: list policy: order fixed before any outcome, may depend on instance and coins, may idle → randomized policy whose start order is, for almost every coin value, one list independent of the outcome; start times unrestricted; reason: same class of policies
--   - encoding: M jobs of each type i → job j ∈ {0, …, bM − 1} has type ⌊j/M⌋; reason: labels are immaterial
-- source:
--   Junho Hwang, A QPTAS for Stochastic Scheduling of Bernoulli Jobs, STOC 2027 submission #427 (October 2026), PDF SHA-256 5d2e3fc3a3b47830c7018375aacf3e77df7f0e30725fecb62845334a8f0be7a9, Theorem 7.1, p. 20 (proof pp. 20–21); Theorem 1.5, p. 4

import Definitions.Def_BernoulliQPTAS_Scheduling_Supplement_Sampling

open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace BernoulliQPTAS.Scheduling.Supplement

open BernoulliQPTAS.Scheduling

theorem theorem_7_1 (b : ℕ) (hb : 2 ≤ b) :
    let I := listInstance b
    let M : ℝ := 2 ^ b
    let OPT := optimum I (initialState Finset.univ)
    (∀ π : RandomPolicy (b * 2 ^ b) 2, RandomAdmissible I (initialState Finset.univ) π →
        IsListPolicy π →
        ENNReal.ofReal (M * b ^ 2 / 128) ≤ randomCost I π ∧
          ENNReal.ofReal ((b : ℝ) / 768) * OPT ≤ randomCost I π) ∧
      OPT ≤ ENNReal.ofReal (6 * M * b) ∧
      Real.logb 2 ((b : ℝ) * M) / 1536 ≤ (b : ℝ) / 768 := by sorry

end BernoulliQPTAS.Scheduling.Supplement
