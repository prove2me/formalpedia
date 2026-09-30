-- Prove2me | Theorems.Thm_ComputationalLearning_statistics_conjunction_error
-- name    : ComputationalLearning.statistics_conjunction_error
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:22:36.033987+00:00
-- url     : https://prove2.me/theorems/d8648168-bec2-43ac-a533-1cd3a492c191
-- title:
--   §5.2: the conjunction of all significant, non-harmful literals has error at most ε/2 (the analysis behind Theorem 5.2)
-- statement:
--   **§5.2** (p. 107). We say that $z$ is significant if $p_0(z) \ge \epsilon/8n$ and harmful if $p_{01}(z) \ge \epsilon/8n$. We now argue that if $h$ is the conjunction of all the significant literals that are not harmful, then $h$ has error less than $\epsilon$ with respect to $c$ and $D$: $\Pr[c(a) = 0 \wedge h(a) = 1]$ is at most the probability that some insignificant literal is $0$ in $a$, at most $2n(\epsilon/8n) = \epsilon/4$ by the union bound; $\Pr[c(a) = 1 \wedge h(a) = 0]$ is at most the probability that some harmful literal is $0$ in $a$ with $c(a) = 1$, at most $\epsilon/4$; thus $\mathrm{error}(h) \le \epsilon/2$.
--
--   Formally: for every target conjunction $T$ over $x_1, \dots, x_n$, every distribution $D$ on $\{0,1\}^n$ and $\epsilon > 0$, the conjunction of the significant non-harmful literals has error at most $\epsilon/2$ with respect to $\mathrm{evalConj}\,T$ and $D$. This is the exact-probability content of Theorem 5.2 (conjunctions are learnable from statistical queries with tolerance $\epsilon/8n$).
-- source:
--   Kearns and Vazirani, An Introduction to Computational Learning Theory, MIT Press 1994, doi:10.7551/mitpress/3897.001.0001, §5.2 pp. 106-108, the algorithm for learning conjunctions from statistics and its error analysis

import Definitions.Def_ComputationalLearning_Noise

open MeasureTheory ProbabilityTheory

namespace ComputationalLearning

/-- **Learning conjunctions from statistics** (§5.2, p. 107; the analysis behind Theorem 5.2). For
a target conjunction `c` over `x₁, …, xₙ`, a distribution `D` and `ε > 0`, if `h` is the
conjunction of all the significant literals (`p₀(z) ≥ ε/8n`) that are not harmful
(`p₀₁(z) < ε/8n`), then `error(h) ≤ ε/4 + ε/4 = ε/2`: a false positive requires an insignificant
literal of `c` to be `0`, a false negative a harmful literal of `h` to be `0` on a positive
example, and the union bound over the `2n` literals gives `ε/4` each. -/
theorem statistics_conjunction_error {n : ℕ} (T : Conjunction (Fin n)) (D : Measure (Cube (Fin n)))
    [IsProbabilityMeasure D] {ε : ℝ} (hε : 0 < ε) :
    errorOf D (evalConj T) (evalConj (statisticsConj D (evalConj T) ε)) ≤ ε / 2 := by sorry

end ComputationalLearning
