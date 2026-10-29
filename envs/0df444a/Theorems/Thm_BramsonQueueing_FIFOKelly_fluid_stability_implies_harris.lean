-- Prove2me | Theorems.Thm_BramsonQueueing_FIFOKelly_fluid_stability_implies_harris
-- name    : BramsonQueueing.FIFOKelly.fluid_stability_implies_harris
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T05:09:43.666987+00:00
-- url     : https://prove2.me/theorems/a8d09084-a3ec-4ea0-956c-9ebd0abbd7a1
-- title:
--   Theorem 4.16 — fluid stability implies positive Harris recurrence
-- statement:
--   Consider a general HL queueing network. Suppose every set $\{x:|x|\le\kappa\}$, for $\kappa>0$, is petite. If one $N>0$ drains every fluid limit by time $N|\bar Z(0)|$, then the stochastic network is positive Harris recurrent:
--   $$\operatorname{StableFluidLimits}(X)\ \Longrightarrow\ \operatorname{PositiveHarris}(X).$$
--   Also, for every associated fluid model, stability of that model implies positive Harris recurrence of the network. Both conclusions are included in this item. Positive Harris recurrence uses infinite occupation of positive irreducibility-measure sets and an invariant probability law; it is not replaced by a Lyapunov inequality or ordinary countable-state recurrence.
--
--   Differences from the source:
--   - encoding: finitely many classes and stations, with nonnegative real time → Fin K and Fin J, real functions restricted to nonnegative time; reason: finite index relabelling and time representation preserve every source instance
--   - encoding: the general HL process of Section 4.1 → a metric identification with ordered finite job lists and an explicit primitive-driven event trace; reason: the coordinates, metric, clocks, allocation updates and full unbounded state domain represent the source process independently of stability
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9, Theorem 4.16, printed [121], PDF [129]

import Definitions.Def_BramsonQueueing_FIFOKelly_Limits

namespace BramsonQueueing.FIFOKelly

theorem fluid_stability_implies_harris {K J : ℕ} {S Ω : Type} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] [LocallyCompactSpace S]
    [TopologicalSpace.SeparableSpace S] [MeasurableSpace Ω] (N : HLNetwork K J S Ω) (hp : PetiteSublevels N) :
    (FluidStable (IsFluidLimit N) → PositiveHarris N.process) ∧
    (∀ M : FluidModel K J, Associated N M → FluidStable M.Solution →
      PositiveHarris N.process) := by sorry

end BramsonQueueing.FIFOKelly
