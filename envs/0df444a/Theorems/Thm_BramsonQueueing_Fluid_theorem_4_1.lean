-- Prove2me | Theorems.Thm_BramsonQueueing_Fluid_theorem_4_1
-- name    : BramsonQueueing.Fluid.theorem_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:19:04.017528+00:00
-- url     : https://prove2.me/theorems/47d1a440-ceb9-4f89-8648-866e6f989efa
-- title:
--   Theorem 4.1 — Harris recurrence and delayed petite-set return criteria
-- statement:
--   Let $X$ be a Borel-right strong Markov process on the locally compact separable metric Borel state space of Section 4.1. Write $\tau_A=\inf\{t\ge0:X(t)\in A\}$ and $\tau_A(\delta)=\inf\{t\ge\delta:X(t)\in A\}$. Then:
--
--   1. $X$ is Harris recurrent if and only if some closed petite set $A$ satisfies
--   $$\mathbb P_x(\tau_A<\infty)=1\quad\text{for every }x.$$
--   2. If $X$ is Harris recurrent, it is positive Harris recurrent if and only if some closed petite set $A$ satisfies
--   $$\sup_{x\in A}\mathbb E_x\tau_A(\delta)<\infty$$
--   for some $\delta>0$. Equivalently, such an $A$ can be chosen so that the bound holds for every $\delta>0$, with its finite bound allowed to depend on $\delta$.
--
--   This characterizes recurrence independently of a drift condition and supplies the return-time criterion used by the Foster results.
--
--   Differences from the source:
--   - encoding: nonnegative real times and nonnegative quantities → NNReal times and quantities; reason: the subtype has the same domain, including zero
--   - encoding: possibly infinite nonnegative expectations → ENNReal lower Lebesgue integrals; reason: infinite expectation remains infinite rather than taking the default value of a real integral
--   - encoding: uniform limits or finite suprema → epsilon-threshold statements or one finite bound uniform over the stated indices; reason: these are equivalent and avoid default values for unbounded real suprema
--   - encoding: the universally completed natural filtration in (4.5) → usual completed filtrations indexed by the starting state, with explicit strong Markov identities; reason: the canonical Markov family admits these completed starting-state realizations with the same paths and transition laws
--   - encoding: a finite nonzero stationary measure in positive Harris recurrence → an invariant probability measure; reason: division by the finite positive total mass preserves invariance and is reversible by taking the probability itself
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9; published edition; Theorem 4.1, printed 89 / PDF 97.

import Definitions.Def_BramsonQueueing_Fluid_MarkovProcess

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace BramsonQueueing.Fluid

theorem theorem_4_1 {S Ω : Type*} [MetricSpace S] [MeasurableSpace S]
    [BorelSpace S] [LocallyCompactSpace S] [SecondCountableTopology S]
    [MeasurableSpace Ω] (p : MarkovProcess S Ω) :
    (Harris p ↔ ∃ A : Set S, IsClosed A ∧ Petite p A ∧
      ∀ x, p.law x {ω | hittingTime p A 0 x ω < ⊤} = 1) ∧
    (Harris p →
      (PositiveHarris p ↔ ∃ A : Set S, IsClosed A ∧ Petite p A ∧
        ∃ δ : ℝ≥0, 0 < δ ∧ ∃ M : ℝ≥0, ∀ x ∈ A, expectedHitting p A δ x ≤ M) ∧
      (PositiveHarris p ↔ ∃ A : Set S, IsClosed A ∧ Petite p A ∧
        ∀ δ : ℝ≥0, 0 < δ → ∃ M : ℝ≥0, ∀ x ∈ A, expectedHitting p A δ x ≤ M)) := by sorry

end BramsonQueueing.Fluid
