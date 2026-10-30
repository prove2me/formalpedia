-- Prove2me | Theorems.Thm_BSSSampleRobust_Asymptotic_theorem_1b
-- name    : BSSSampleRobust.Asymptotic.theorem_1b
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T22:28:33.778202+00:00
-- url     : https://prove2.me/theorems/5918899e-4b4b-4940-b011-1aa2cf014cba
-- title:
--   Theorem 1b — Upper asymptotic bound
-- statement:
--   Fix a positive ambient dimension $d$, any $\ell_p$ norm with $1\le p\le\infty$, and a joint Borel probability law $P$ on $\mathbb R^d$. Complete trajectories are sampled independently with law $P$; coordinates within a trajectory may be arbitrarily dependent. Let $S$ be its topological support and $\Xi$ a known convex superset of $S$, with $P(\Xi)=1$. For the first $N$ samples, set $U_N^j=\{z\in\Xi:\|z-\hat\xi^j\|\le\epsilon_N\}$ and $S_N=\bigcup_{j=1}^N U_N^j$.
--
--   Consider any finite horizon $T\ge1$, stage dimensions $d_t,n_t$, and $0\le p_t\le n_t$ integer coordinates, with $d=\sum_t d_t>0$. A policy $x_t$ is any Borel measurable function of $\xi_{<t}$ into $\mathbb R^{n_t-p_t}\times\mathbb Z^{p_t}$; it is selected before $\xi_t$ is observed. Costs $c_t$, matrices $A_t$, and right-hand side $b$ are affine functions of the entire trajectory. Write $F_x(z)=\sum_t c_t(z)\cdot x_t(z_{<t})$ and impose the componentwise constraints $\sum_t A_t(z)x_t(z_{<t})\le b(z)$. Let $\widehat J_N$ be the infimum of $N^{-1}\sum_j\sup_{z\in U_N^j}F_x(z)$ over policies feasible at every point of $S_N$. All values are extended real, with the positive-part-first expectation convention $\infty-\infty=+\infty$.
--
--   The lower endpoint $\underline J$ is the limit as $\rho\downarrow0$ of the infimum of $\mathbb E_P[F_x(\xi)I\{\xi\in Z\}]$ over both $x$ and $Z\subseteq\Xi$, with pointwise feasibility on $Z$ and $P(Z)\ge1-\rho$. Define $\overline E_P F_x=\lim_{r\downarrow0}\mathbb E_P[\sup_{z\in\Xi:\|z-\xi\|\le r}F_x(z)]$. The upper endpoint $\overline J$ is the limit as $\rho\downarrow0$ of the infimum of $\overline E_P F_x$ over policies feasible on $\{z\in\Xi:\operatorname{dist}(z,S)\le\rho\}$. Suppose only Assumption 2: for some $\kappa>0$, $\epsilon_N=\kappa N^{-1/\max\{3,d+1\}}$ for every $N\ge1$. Then
--   $$\limsup_{N\to\infty}\widehat J_N\le\overline J\qquad P^\infty\text{-almost surely}.$$
--   No light-tail or value-preserving growth assumption is made. The upper endpoint uses the limit of expectations of local suprema and feasibility on the expanded support.
--
--   Differences from the source:
--   - encoding: finite-dimensional real spaces with any fixed lp norm, 1 ≤ p ≤ ∞ → PiLp over finite coordinates, Borel sigma algebras, and Fact (1 ≤ p); reason: coordinate relabeling preserves every allowed norm and every source instance; the ambient dimension is positive
--   - encoding: extended-real expectation and extrema with infinity minus infinity equal to positive infinity → EReal extrema and the referenced positive-part-first expectation, applied on the completed measure; reason: infeasibility gives positive infinity and unbounded extrema remain infinite; no integrability hypothesis is added
--   - reading: expectations of local suprema and indicators, with page 6 defining set probability as indicator expectation but not specifying completion → completed lower-integral expectations; concentration and retained-set probabilities are expectations of indicators; reason: this preserves the explicit indicator identity without imposing measurability, closedness, continuity, or boundedness; on completed-measurable sets it is the ordinary probability
--   - encoding: samples indexed 1 through N, N positive, under the infinite iid product law → samples indexed by Fin N, drawn from the coordinates 0 through N-1 of Measure.infinitePi on natural numbers; reason: a shift of labels gives the same iid data; finite-sample assertions require N ≥ 1 and asymptotic assertions ignore N = 0
--   - encoding: measurable maps from each strict history into a real block times an integer block → measurable real coordinate maps with an integral suffix, and histories indexed by precisely the coordinates at earlier stages; reason: the integer lattice has the induced Borel structure, so this represents exactly the same mixed-integer policy space, including the singleton first-stage history
--   - encoding: limits as rho decreases to zero and a local upper envelope defined as a limit of expectations → a supremum over 0 < rho < 1 for the lower value, and separate infima over positive envelope and support radii for the upper value; reason: these are the same monotone extended-real limits; the order of expectation, envelope, policy infimum and support limit is preserved
-- source:
--   Bertsimas, Shtern and Sturt (2023), A Data-Driven Approach to Multistage Stochastic Linear Optimization, Management Science, https://doi.org/10.1287/mnsc.2022.4352; published basis, supplied manuscript/e-companion artifact; Theorem 1b, PDF page 56, printed page ec14

import Mathlib
import Definitions.Def_BSSSampleRobust_Asymptotic_Values

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BSSSampleRobust.Asymptotic

theorem theorem_1b (p : ℝ≥0∞) [Fact (1 ≤ p)] (D : Layout)
    (M : LinearModel p D) (S : Sampling p (Coord D)) (ε : ℕ → ℝ)
    (h2 : radiusRate (∑ t, D.d t) ε) :
    ∀ᵐ ω ∂sampleLaw S, limsup (sampleValue M S ω ε) atTop ≤ upperValue M S := by sorry

end BSSSampleRobust.Asymptotic
