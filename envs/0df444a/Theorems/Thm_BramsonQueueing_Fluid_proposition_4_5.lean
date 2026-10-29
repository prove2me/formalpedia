-- Prove2me | Theorems.Thm_BramsonQueueing_Fluid_proposition_4_5
-- name    : BramsonQueueing.Fluid.proposition_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:19:48.840426+00:00
-- url     : https://prove2.me/theorems/4ae2e2be-d16f-4e81-8a6a-0d563040bf4d
-- title:
--   Proposition 4.5 — Generalized Foster's criterion
-- statement:
--   Let $X$ have the general-state Markov regularity of Section 4.1, and let $|x|$ be a nonnegative measurable size. Suppose $\epsilon,\kappa,\delta>0$ and a measurable sampling function $g$ satisfy $g(x)\ge\delta$ and
--   $$\mathbb E_x|X(g(x))|\le(|x|\vee\kappa)-\epsilon g(x)\quad\text{for every }x.$$
--   For $A=\{x:|x|\le\kappa\}$, the delayed hitting time satisfies
--   $$\mathbb E_x\tau_A(\delta)\le\frac{|x|\vee\kappa}{\epsilon}\quad\text{for every }x.$$
--   If $A$ is closed and petite, $X$ is positive Harris recurrent. If $A$ is closed and uniformly small on some interval $[s_1,s_2]$ with $0<s_1<s_2$, $X$ is ergodic. No continuity or properness of the size is imposed; closedness is required only in the two conditional recurrence conclusions.
--
--   Differences from the source:
--   - encoding: nonnegative real times and nonnegative quantities → NNReal times and quantities; reason: the subtype has the same domain, including zero
--   - encoding: possibly infinite nonnegative expectations → ENNReal lower Lebesgue integrals; reason: infinite expectation remains infinite rather than taking the default value of a real integral
--   - encoding: expected size at most maximum size minus epsilon times sampling time → expected size plus epsilon times sampling time at most maximum size; reason: equivalent rearrangement avoids subtraction of extended quantities
--   - encoding: the universally completed natural filtration in (4.5) → usual completed filtrations indexed by the starting state, with explicit strong Markov identities; reason: the canonical Markov family admits these completed starting-state realizations with the same paths and transition laws
--   - encoding: a finite nonzero stationary measure in positive Harris recurrence → an invariant probability measure; reason: division by the finite positive total mass preserves invariance and is reversible by taking the probability itself
--   - encoding: convergence in the total variation norm in (4.22) → event-uniform epsilon bounds for transition and invariant probabilities; reason: the event supremum differs from the signed-measure norm by at most its fixed factor-two convention, which does not change convergence to zero
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9; published edition; Proposition 4.5, printed 93 / PDF 101, equations (4.26)–(4.27).

import Definitions.Def_BramsonQueueing_Fluid_MarkovProcess

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace BramsonQueueing.Fluid

theorem proposition_4_5 {S Ω : Type*} [MetricSpace S] [MeasurableSpace S]
    [BorelSpace S] [LocallyCompactSpace S] [SecondCountableTopology S]
    [MeasurableSpace Ω] (p : MarkovProcess S Ω) (size : S → ℝ≥0)
    (hsize : Measurable size) (g : S → ℝ≥0) (hg : Measurable g)
    (ε κ δ : ℝ≥0) (hε : 0 < ε) (hκ : 0 < κ) (hδ : 0 < δ)
    (hdelay : ∀ x, δ ≤ g x)
    (hdrift : ∀ x, expectedSize p size x (g x) + (ε * g x : ℝ≥0) ≤
      (max (size x) κ : ℝ≥0)) :
    (∀ x, expectedHitting p {y | size y ≤ κ} δ x ≤ (max (size x) κ / ε : ℝ≥0)) ∧
    (IsClosed {x | size x ≤ κ} → Petite p {x | size x ≤ κ} → PositiveHarris p) ∧
    (IsClosed {x | size x ≤ κ} → ∀ s₁ s₂ : ℝ≥0, 0 < s₁ → s₁ < s₂ →
      UniformlySmall p {x | size x ≤ κ} s₁ s₂ → Ergodic p) := by sorry

end BramsonQueueing.Fluid
