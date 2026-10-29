-- Prove2me | Theorems.Thm_BramsonQueueing_Fluid_proposition_4_6
-- name    : BramsonQueueing.Fluid.proposition_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:19:10.086527+00:00
-- url     : https://prove2.me/theorems/e817c762-b37e-4006-bd20-5203bc6f95a2
-- title:
--   Proposition 4.6 — Multiplicative Foster's criterion
-- statement:
--   Let $X$ be the general-state Markov process of Section 4.1, with a nonnegative measurable size $|x|$. Suppose $c,\epsilon,\kappa>0$ satisfy
--   $$\mathbb E_x|X(c(|x|\vee\kappa))|\le(1-\epsilon)(|x|\vee\kappa)\quad\text{for every }x.$$
--   Set $A=\{x:|x|\le\kappa\}$. If $A$ is closed and petite then $X$ is positive Harris recurrent. If $A$ is closed and uniformly small on an interval $[s_1,s_2]$ with $0<s_1<s_2$, then $X$ is ergodic.
--
--   The sampling horizon is proportional to the current size outside the sublevel set. Both recurrence and ergodicity conclusions are retained.
--
--   Differences from the source:
--   - encoding: nonnegative real times and nonnegative quantities → NNReal times and quantities; reason: the subtype has the same domain, including zero
--   - encoding: possibly infinite nonnegative expectations → ENNReal lower Lebesgue integrals; reason: infinite expectation remains infinite rather than taking the default value of a real integral
--   - encoding: expected size at most (1-epsilon) times maximum size → expected size plus epsilon times maximum size at most maximum size; reason: the equivalent rearrangement retains the full epsilon domain and avoids truncated subtraction
--   - encoding: the universally completed natural filtration in (4.5) → usual completed filtrations indexed by the starting state, with explicit strong Markov identities; reason: the canonical Markov family admits these completed starting-state realizations with the same paths and transition laws
--   - encoding: a finite nonzero stationary measure in positive Harris recurrence → an invariant probability measure; reason: division by the finite positive total mass preserves invariance and is reversible by taking the probability itself
--   - encoding: convergence in the total variation norm in (4.22) → event-uniform epsilon bounds for transition and invariant probabilities; reason: the event supremum differs from the signed-measure norm by at most its fixed factor-two convention, which does not change convergence to zero
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9; published edition; Proposition 4.6, printed 94 / PDF 102, equation (4.28).

import Definitions.Def_BramsonQueueing_Fluid_MarkovProcess

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace BramsonQueueing.Fluid

theorem proposition_4_6 {S Ω : Type*} [MetricSpace S] [MeasurableSpace S]
    [BorelSpace S] [LocallyCompactSpace S] [SecondCountableTopology S]
    [MeasurableSpace Ω] (p : MarkovProcess S Ω) (size : S → ℝ≥0)
    (hsize : Measurable size) (c ε κ : ℝ≥0) (hc : 0 < c) (hε : 0 < ε) (hκ : 0 < κ)
    (hdrift : ∀ x, expectedSize p size x (c * max (size x) κ) +
      (ε * max (size x) κ : ℝ≥0) ≤ (max (size x) κ : ℝ≥0)) :
    (IsClosed {x | size x ≤ κ} → Petite p {x | size x ≤ κ} → PositiveHarris p) ∧
    (IsClosed {x | size x ≤ κ} → ∀ s₁ s₂ : ℝ≥0, 0 < s₁ → s₁ < s₂ →
      UniformlySmall p {x | size x ≤ κ} s₁ s₂ → Ergodic p) := by sorry

end BramsonQueueing.Fluid
