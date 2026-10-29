-- Prove2me | Theorems.Thm_BramsonQueueing_Fluid_proposition_4_15
-- name    : BramsonQueueing.Fluid.proposition_4_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:22:46.051038+00:00
-- url     : https://prove2.me/theorems/413c818f-a872-48ea-bfd9-647d6d6e3252
-- title:
--   Proposition 4.15 — Residual arrival and service bounds and limits
-- statement:
--   For every subcritical HL queueing network there is one $c_0\ge1$ such that for every $c\ge c_0$,
--   $$|U^x(c|x|)|/|x|\to0,\qquad |V^x(c|x|)|/|x|\to0\quad\text{on }G\text{ as }|x|\to\infty.$$
--   Both uniform expectation bounds hold:
--   $$\sup_{t\ge1}\sup_{|x|\le t}\mathbb E|U^x(t)|/t<\infty,\qquad \sup_{t\ge1}\sup_{|x|\le t}\mathbb E|V^x(t)|/t<\infty.$$
--   For the same range of $c$, both expectations vanish under state-size scaling:
--   $$\mathbb E|U^x(c|x|)|/|x|\to0,\qquad\mathbb E|V^x(c|x|)|/|x|\to0.$$
--   All these conclusions also hold whenever the associated family of fluid limits is stable. The stability alternative is a separate implication and does not assume subcriticality as an extra hypothesis.
--
--   Differences from the source:
--   - encoding: classes 1 through K and stations 1 through J → Fin K and Fin J, with positive cardinalities and an onto station assignment; reason: this only relabels the finite classes and nonempty stations; queue populations remain unbounded
--   - encoding: nonnegative real times and nonnegative quantities → NNReal times and quantities; reason: the subtype has the same domain, including zero
--   - encoding: the full HL state and primitive-driven process of Sections 4.1 and 4.3 → an equivalent ordered-list state presentation and an axiomatic realization of that evolution; reason: the coordinate equivalence includes every source state; the fields specify dynamics and Markov regularity, not stability conclusions
--   - encoding: possibly infinite nonnegative expectations → ENNReal lower Lebesgue integrals; reason: infinite expectation remains infinite rather than taking the default value of a real integral
--   - encoding: uniform limits or finite suprema → epsilon-threshold statements or one finite bound uniform over the stated indices; reason: these are equivalent and avoid default values for unbounded real suprema
--   - reading: the second denominator of (4.93) is printed as x → the denominator is the state size |x|; reason: x is a structured state and the proof ends on printed p.121 / PDF p.129 with exactly this norm denominator; see insight I1
--   - encoding: the universally completed natural filtration in (4.5) → usual completed filtrations indexed by the starting state, with explicit strong Markov identities; reason: the canonical Markov family admits these completed starting-state realizations with the same paths and transition laws
--   - encoding: the primitive construction for each initial state in Section 4.1 and the common event G in (4.70) → one probability space of positive primitive sequences, with the initial state a parameter of the paths; reason: the iid primitive laws do not depend on the initial state; positive versions can be realized on their positive product space and completed without restricting any permitted law
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9; published edition; Proposition 4.15, printed 119 / PDF 127, equations (4.91)–(4.93); proof concludes printed 121 / PDF 129.

import Definitions.Def_BramsonQueueing_Fluid_FluidLimits

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace BramsonQueueing.Fluid

theorem proposition_4_15 {K J : ℕ} {d : NetworkData K J} {S Ω : Type*}
    [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace Ω]
    (n : HLNetwork d S Ω) :
    (Subcritical d → ResidualConclusions n) ∧
    (FluidLimitsStable n → ResidualConclusions n) := by sorry

end BramsonQueueing.Fluid
