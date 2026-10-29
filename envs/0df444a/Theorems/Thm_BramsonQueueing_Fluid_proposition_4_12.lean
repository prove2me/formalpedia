-- Prove2me | Theorems.Thm_BramsonQueueing_Fluid_proposition_4_12
-- name    : BramsonQueueing.Fluid.proposition_4_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:23:05.165364+00:00
-- url     : https://prove2.me/theorems/0628a4ea-1e56-4de8-a4cd-4550ede55a14
-- title:
--   Proposition 4.12 — Six-component fluid compactness and basic-model association
-- statement:
--   For an HL queueing network, fix any sample $\omega$ in the common primitive strong-law event $G$. Every sequence $(a_n,x_n)$ satisfying
--   $$a_n\to\infty,\quad\limsup_n|z_n|/a_n<\infty,\quad |u_n|/a_n\to0,\quad |v_n|/a_n\to0$$
--   has a subsequence on which
--   $$\overline{\mathcal X}(t)=\lim_n\frac{\mathcal X^{x_{i_n}}(a_{i_n}t)}{a_{i_n}}$$
--   exists uniformly on compact time intervals in all six components $(A,D,T,W,Y,Z)$. The limit satisfies the basic fluid equations (4.50)–(4.55) with the corresponding primitive means. Consequently the network is associated with its basic fluid model.
--
--   The assertion is pathwise for every sample in $G$, not merely convergence in distribution or compactness of selected components.
--
--   Differences from the source:
--   - encoding: classes 1 through K and stations 1 through J → Fin K and Fin J, with positive cardinalities and an onto station assignment; reason: this only relabels the finite classes and nonempty stations; queue populations remain unbounded
--   - encoding: nonnegative real times and nonnegative quantities → NNReal times and quantities; reason: the subtype has the same domain, including zero
--   - encoding: the full HL state and primitive-driven process of Sections 4.1 and 4.3 → an equivalent ordered-list state presentation and an axiomatic realization of that evolution; reason: the coordinate equivalence includes every source state; the fields specify dynamics and Markov regularity, not stability conclusions
--   - encoding: finite limsup of the nonnegative initial queue-size ratios → one finite bound on all ratios; reason: each scale is positive, so the finitely many early ratios are finite and the formulations are equivalent
--   - encoding: the universally completed natural filtration in (4.5) → usual completed filtrations indexed by the starting state, with explicit strong Markov identities; reason: the canonical Markov family admits these completed starting-state realizations with the same paths and transition laws
--   - encoding: the primitive construction for each initial state in Section 4.1 and the common event G in (4.70) → one probability space of positive primitive sequences, with the initial state a parameter of the paths; reason: the iid primitive laws do not depend on the initial state; positive versions can be realized on their positive product space and completed without restricting any permitted law
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9; published edition; Proposition 4.12, printed 113 / PDF 121, with (4.71)–(4.72) on printed 111–112 / PDF 119–120.

import Definitions.Def_BramsonQueueing_Fluid_FluidLimits

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace BramsonQueueing.Fluid

theorem proposition_4_12 {K J : ℕ} {d : NetworkData K J} {S Ω : Type*}
    [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace Ω]
    (n : HLNetwork d S Ω) :
    (∀ ω, PrimitiveGood n.primitives ω → ∀ a x, AdmissibleScaling n a x →
      ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ q : SixPath K J,
        SixUOC (fun i => scaleSix (a (r i)) (n.path (x (r i)) ω)) q ∧ BasicFluid d q) ∧
    Associated n (basicModel d) := by sorry

end BramsonQueueing.Fluid
