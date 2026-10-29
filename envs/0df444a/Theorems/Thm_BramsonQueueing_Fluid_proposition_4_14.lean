-- Prove2me | Theorems.Thm_BramsonQueueing_Fluid_proposition_4_14
-- name    : BramsonQueueing.Fluid.proposition_4_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:22:57.55429+00:00
-- url     : https://prove2.me/theorems/03e79ba2-1669-408d-92ab-e10c9c438cee
-- title:
--   Proposition 4.14 — Queue-length growth and uniform integrability
-- statement:
--   For any HL queueing network, every $c>0$ and every sample $\omega\in G$ satisfy
--   $$\limsup_{|x|\to\infty}\frac{|Z^x(c|x|)|}{|x|}\le c|\alpha|+1.$$
--   Moreover,
--   $$\sup_{t\ge1}\sup_{|x|\le t}\mathbb E[|Z^x(t)|/t;\ |Z^x(t)|\ge Mt]\longrightarrow0\quad(M\to\infty),$$
--   and in particular
--   $$\sup_{t\ge1}\sup_{|x|\le t}\frac{\mathbb E|Z^x(t)|}{t}<\infty.$$
--   The initial size includes queue mass and both residual-time vectors. Both supremum indices range over their full source domains; the pathwise threshold may depend on $c$, the sample, and the error tolerance.
--
--   Differences from the source:
--   - encoding: classes 1 through K and stations 1 through J → Fin K and Fin J, with positive cardinalities and an onto station assignment; reason: this only relabels the finite classes and nonempty stations; queue populations remain unbounded
--   - encoding: nonnegative real times and nonnegative quantities → NNReal times and quantities; reason: the subtype has the same domain, including zero
--   - encoding: the full HL state and primitive-driven process of Sections 4.1 and 4.3 → an equivalent ordered-list state presentation and an axiomatic realization of that evolution; reason: the coordinate equivalence includes every source state; the fields specify dynamics and Markov regularity, not stability conclusions
--   - encoding: possibly infinite nonnegative expectations → ENNReal lower Lebesgue integrals; reason: infinite expectation remains infinite rather than taking the default value of a real integral
--   - encoding: uniform limits or finite suprema → epsilon-threshold statements or one finite bound uniform over the stated indices; reason: these are equivalent and avoid default values for unbounded real suprema
--   - encoding: the universally completed natural filtration in (4.5) → usual completed filtrations indexed by the starting state, with explicit strong Markov identities; reason: the canonical Markov family admits these completed starting-state realizations with the same paths and transition laws
--   - encoding: the primitive construction for each initial state in Section 4.1 and the common event G in (4.70) → one probability space of positive primitive sequences, with the initial state a parameter of the paths; reason: the iid primitive laws do not depend on the initial state; positive versions can be realized on their positive product space and completed without restricting any permitted law
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9; published edition; Proposition 4.14, printed 118 / PDF 126, equations (4.87)–(4.89).

import Definitions.Def_BramsonQueueing_Fluid_FluidLimits

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace BramsonQueueing.Fluid

theorem proposition_4_14 {K J : ℕ} {d : NetworkData K J} {S Ω : Type*}
    [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace Ω]
    (n : HLNetwork d S Ω) :
    (∀ c : ℝ≥0, 0 < c → ∀ ω, PrimitiveGood n.primitives ω →
      ∀ ε : ℝ, 0 < ε → ∃ R : ℝ≥0, ∀ x, R ≤ n.size x →
        (n.zMass (n.process.X x (c * n.size x) ω) : ℝ) / n.size x ≤
          c * mass d.alpha + 1 + ε) ∧
    (∀ ε : ℝ≥0, 0 < ε → ∃ M₀ : ℝ≥0, ∀ M ≥ M₀, ∀ t : ℝ≥0, 1 ≤ t →
      ∀ x, n.size x ≤ t →
        (∫⁻ ω in {ω | M * t ≤ n.zMass (n.process.X x t ω)},
          (n.zMass (n.process.X x t ω) : ℝ≥0∞) / t ∂n.μ) ≤ ε) ∧
    (∃ C : ℝ≥0, ∀ t : ℝ≥0, 1 ≤ t → ∀ x, n.size x ≤ t →
      (∫⁻ ω, (n.zMass (n.process.X x t ω) : ℝ≥0∞) ∂n.μ) / t ≤ C) := by sorry

end BramsonQueueing.Fluid
