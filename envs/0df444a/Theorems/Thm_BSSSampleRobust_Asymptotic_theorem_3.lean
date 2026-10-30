-- Prove2me | Theorems.Thm_BSSSampleRobust_Asymptotic_theorem_3
-- name    : BSSSampleRobust.Asymptotic.theorem_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T22:27:40.615601+00:00
-- url     : https://prove2.me/theorems/96723611-d54f-4c27-967a-ab1c6c9a5b23
-- title:
--   Theorem 3 — Support coverage rate
-- statement:
--   Fix a positive ambient dimension $d$, any $\ell_p$ norm with $1\le p\le\infty$, and a joint Borel probability law $P$ on $\mathbb R^d$. Complete trajectories are sampled independently with law $P$; coordinates within a trajectory may be arbitrarily dependent. Let $S$ be its topological support and $\Xi$ a known convex superset of $S$, with $P(\Xi)=1$. For the first $N$ samples, set $U_N^j=\{z\in\Xi:\|z-\hat\xi^j\|\le\epsilon_N\}$ and $S_N=\bigcup_{j=1}^N U_N^j$.
--
--   Assumption 1 means $\mathbb E_P[\exp(\|\xi\|^a)]<\infty$ for some $a>1$. Assumption 2 means $\epsilon_N=\kappa N^{-1/\max\{3,d+1\}}$ for some $\kappa>0$ and every $N\ge1$. Under Assumptions 1 and 2, $P^\infty$-almost surely,
--   $$\lim_{N\to\infty}\frac{N^{1/(d+1)}}{(\log N)^{d+1}}P(\xi\notin S_N)=0.$$
--   The probability inside the limit is evaluated under $P$ with the training sequence fixed. The conclusion retains the scaled missing-mass rate.
--
--   Differences from the source:
--   - encoding: finite-dimensional real spaces with any fixed lp norm, 1 ≤ p ≤ ∞ → PiLp over finite coordinates, Borel sigma algebras, and Fact (1 ≤ p); reason: coordinate relabeling preserves every allowed norm and every source instance; the ambient dimension is positive
--   - encoding: extended-real expectation and extrema with infinity minus infinity equal to positive infinity → EReal extrema and the referenced positive-part-first expectation, applied on the completed measure; reason: infeasibility gives positive infinity and unbounded extrema remain infinite; no integrability hypothesis is added
--   - reading: expectations of local suprema and indicators, with page 6 defining set probability as indicator expectation but not specifying completion → completed lower-integral expectations; concentration and retained-set probabilities are expectations of indicators; reason: this preserves the explicit indicator identity without imposing measurability, closedness, continuity, or boundedness; on completed-measurable sets it is the ordinary probability
--   - encoding: samples indexed 1 through N, N positive, under the infinite iid product law → samples indexed by Fin N, drawn from the coordinates 0 through N-1 of Measure.infinitePi on natural numbers; reason: a shift of labels gives the same iid data; finite-sample assertions require N ≥ 1 and asymptotic assertions ignore N = 0
--   - encoding: probability in the scaled limit is a real number in [0,1] → the measure of the missing-mass event is converted from ENNReal to a real number before scaling; reason: the event is measurable in the completed law because Xi contains the closed full-mass support and the balls are closed; its measure is at most one, so toReal cannot encounter infinity
-- source:
--   Bertsimas, Shtern and Sturt (2023), A Data-Driven Approach to Multistage Stochastic Linear Optimization, Management Science, https://doi.org/10.1287/mnsc.2022.4352; published basis, supplied manuscript/e-companion artifact; Theorem 3, PDF page 15, printed page 15

import Mathlib
import Definitions.Def_BSSSampleRobust_Asymptotic_Sampling

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BSSSampleRobust.Asymptotic

theorem theorem_3 (p : ℝ≥0∞) [Fact (1 ≤ p)] (d : ℕ) (hd : 0 < d)
    (S : Sampling p (Fin d)) (ε : ℕ → ℝ)
    (h1 : lightTail S.law) (h2 : radiusRate d ε) :
    ∀ᵐ ω ∂sampleLaw S,
      Tendsto (fun N => coverageScale d N * (S.law (sampleUnion S ω ε N)ᶜ).toReal)
        atTop (𝓝 (0 : ℝ)) := by sorry

end BSSSampleRobust.Asymptotic
