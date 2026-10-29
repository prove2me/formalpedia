-- Prove2me | Theorems.Thm_BramsonQueueing_FIFOKelly_fluid_limit_compactness
-- name    : BramsonQueueing.FIFOKelly.fluid_limit_compactness
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T05:09:18.362987+00:00
-- url     : https://prove2.me/theorems/17833657-b0f1-4d2a-a468-8f9aab652bb8
-- title:
--   Proposition 4.12 — six-component fluid-limit compactness
-- statement:
--   Fix any HL queueing network and a sample point $\omega$ of its common primitive strong-law event. Every sequence $(a_n,x_n)$ satisfying (4.71) has a strictly increasing subsequence $i_n$ and a six-component limit $\bar X$ such that
--   $$a_{i_n}^{-1}X^{x_{i_n}}(a_{i_n}\,\cdot,\omega)\longrightarrow\bar X$$
--   uniformly on every bounded time interval, and $\bar X$ satisfies all the basic fluid equations with the network's parameters. Consequently the network is associated with its basic fluid model, including subsequential existence and membership of every limit. This is the full pathwise compactness input for the stability transfer theorem.
--
--   Differences from the source:
--   - encoding: finitely many classes and stations, with nonnegative real time → Fin K and Fin J, real functions restricted to nonnegative time; reason: finite index relabelling and time representation preserve every source instance
--   - encoding: the general HL process of Section 4.1 → a metric identification with ordered finite job lists and an explicit primitive-driven event trace; reason: the coordinates, metric, clocks, allocation updates and full unbounded state domain represent the source process independently of stability
--   - encoding: finite limsup of the initial scaled queue size in (4.71) → one upper bound for all terms of that sequence; reason: the scales are positive and every early queue size is finite, so finite limsup and global boundedness are equivalent
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9, Proposition 4.12, printed [113], PDF [121]

import Definitions.Def_BramsonQueueing_FIFOKelly_Limits

namespace BramsonQueueing.FIFOKelly

theorem fluid_limit_compactness {K J : ℕ} {S Ω : Type} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] [LocallyCompactSpace S]
    [TopologicalSpace.SeparableSpace S] [MeasurableSpace Ω] (N : HLNetwork K J S Ω) :
    (∀ ω, GoodPrimitives N.parameters N.primitives ω → ∀ a x,
      AdmissibleScaling N a x → ∃ i : ℕ → ℕ, StrictMono i ∧
        ∃ L, ScaledUOC (a ∘ i) (fun n => networkPaths N (x (i n)) ω) L ∧
          BasicFluid N.parameters L) ∧
    Associated N (basicModel N.parameters) := by sorry

end BramsonQueueing.FIFOKelly
