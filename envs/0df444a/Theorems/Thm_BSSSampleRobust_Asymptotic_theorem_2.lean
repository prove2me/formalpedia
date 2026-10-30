-- Prove2me | Theorems.Thm_BSSSampleRobust_Asymptotic_theorem_2
-- name    : BSSSampleRobust.Asymptotic.theorem_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T22:27:47.211698+00:00
-- url     : https://prove2.me/theorems/0614518a-8cba-4abc-b1eb-720ab02d8ab2
-- title:
--   Theorem 2 — Uniform sample-robust inequality
-- statement:
--   Fix a positive ambient dimension $d$, any $\ell_p$ norm with $1\le p\le\infty$, and a joint Borel probability law $P$ on $\mathbb R^d$. Complete trajectories are sampled independently with law $P$; coordinates within a trajectory may be arbitrarily dependent. Let $S$ be its topological support and $\Xi$ a known convex superset of $S$, with $P(\Xi)=1$. For the first $N$ samples, set $U_N^j=\{z\in\Xi:\|z-\hat\xi^j\|\le\epsilon_N\}$ and $S_N=\bigcup_{j=1}^N U_N^j$.
--
--   Assumption 1 means $\mathbb E_P[\exp(\|\xi\|^a)]<\infty$ for some $a>1$. Assumption 2 means $\epsilon_N=\kappa N^{-1/\max\{3,d+1\}}$ for some $\kappa>0$ and every $N\ge1$. Under Assumptions 1 and 2, $P^\infty$-almost surely there is a single threshold $\bar N$ such that, simultaneously for every $N\ge\bar N$ and every measurable $f:\mathbb R^d\to\mathbb R$,
--   $$E_P[f(\xi)I\{\xi\in S_N\}]\le\frac1N\sum_{j=1}^N\sup_{z\in U_N^j}f(z)+M_N\sup_{z\in S_N}|f(z)|,$$
--   where $M_N=N^{-1/((d+1)(d+2))}\log N$. The null set and threshold are uniform over all measurable functions, including unbounded ones.
--
--   Differences from the source:
--   - encoding: finite-dimensional real spaces with any fixed lp norm, 1 ≤ p ≤ ∞ → PiLp over finite coordinates, Borel sigma algebras, and Fact (1 ≤ p); reason: coordinate relabeling preserves every allowed norm and every source instance; the ambient dimension is positive
--   - encoding: extended-real expectation and extrema with infinity minus infinity equal to positive infinity → EReal extrema and the referenced positive-part-first expectation, applied on the completed measure; reason: infeasibility gives positive infinity and unbounded extrema remain infinite; no integrability hypothesis is added
--   - reading: expectations of local suprema and indicators, with page 6 defining set probability as indicator expectation but not specifying completion → completed lower-integral expectations; concentration and retained-set probabilities are expectations of indicators; reason: this preserves the explicit indicator identity without imposing measurability, closedness, continuity, or boundedness; on completed-measurable sets it is the ordinary probability
--   - encoding: samples indexed 1 through N, N positive, under the infinite iid product law → samples indexed by Fin N, drawn from the coordinates 0 through N-1 of Measure.infinitePi on natural numbers; reason: a shift of labels gives the same iid data; finite-sample assertions require N ≥ 1 and asymptotic assertions ignore N = 0
--   - encoding: an eventual natural-number threshold → an eventual threshold at least 2; reason: increasing a finite threshold preserves the conclusion and ensures a positive error coefficient
-- source:
--   Bertsimas, Shtern and Sturt (2023), A Data-Driven Approach to Multistage Stochastic Linear Optimization, Management Science, https://doi.org/10.1287/mnsc.2022.4352; published basis, supplied manuscript/e-companion artifact; Theorem 2, PDF page 12, printed page 12

import Mathlib
import Definitions.Def_BSSSampleRobust_Asymptotic_Sampling

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BSSSampleRobust.Asymptotic

theorem theorem_2 (p : ℝ≥0∞) [Fact (1 ≤ p)] (d : ℕ) (hd : 0 < d)
    (S : Sampling p (Fin d)) (ε : ℕ → ℝ)
    (h1 : lightTail S.law) (h2 : radiusRate d ε) :
    ∀ᵐ ω ∂sampleLaw S, ∃ K : ℕ, 2 ≤ K ∧ ∀ N : ℕ, K ≤ N →
      ∀ f : Vec p (Fin d) → ℝ, Measurable f →
        expectation S.law (truncated (sampleUnion S ω ε N) f) ≤
          average (fun j : Fin N => supremum (sampleBall S ω ε N j.val) f) +
          scale (uniformError d N) (absSup (sampleUnion S ω ε N) f) := by sorry

end BSSSampleRobust.Asymptotic
