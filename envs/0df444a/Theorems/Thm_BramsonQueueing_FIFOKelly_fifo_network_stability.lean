-- Prove2me | Theorems.Thm_BramsonQueueing_FIFOKelly_fifo_network_stability
-- name    : BramsonQueueing.FIFOKelly.fifo_network_stability
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T05:08:41.119992+00:00
-- url     : https://prove2.me/theorems/8284f435-f887-4f9f-93c8-151096fbdef5
-- title:
--   Theorem 5.9 — stability of subcritical FIFO Kelly networks
-- statement:
--   Consider any open FIFO queueing network of Kelly type with independent positive iid interarrival and service primitives of finite means. Service means are equal within a station; their distributions need not be identical. Suppose the station loads satisfy $\rho_j<1$ and every size sublevel $\{x:|x|\le\kappa\}$, $\kappa>0$, is petite, where $|x|=|z|+|u|+|v|$. Then
--   $$X\text{ is positive Harris recurrent}.$$
--   Thus some nonzero sigma-finite irreducibility measure gives almost surely infinite occupation of its positive-measure sets from every initial state, and the transition semigroup admits an invariant probability measure. This is the stochastic stability result for general renewal and service distributions, on the source's unbounded general state space.
--
--   Differences from the source:
--   - encoding: finitely many classes and stations, with nonnegative real time → Fin K and Fin J, real functions restricted to nonnegative time; reason: finite index relabelling and time representation preserve every source instance
--   - encoding: the general HL process of Section 4.1 → a metric identification with ordered finite job lists and an explicit primitive-driven event trace; reason: the coordinates, metric, clocks, allocation updates and full unbounded state domain represent the source process independently of stability
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9, Theorem 5.9, printed [148], PDF [156]

import Definitions.Def_BramsonQueueing_FIFOKelly_Network

namespace BramsonQueueing.FIFOKelly

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

theorem fifo_network_stability {K J : ℕ} {S Ω : Type} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] [LocallyCompactSpace S]
    [TopologicalSpace.SeparableSpace S] [MeasurableSpace Ω] (N : HLNetwork K J S Ω)
    (hf : ∀ x : S, ∀ k,
      N.discipline (N.coordinates x).val k =
        if (((N.coordinates x).val.jobs.find?
          (fun q => N.parameters.data.p q.1 = N.parameters.data.p k)).map Prod.fst) = some k
        then 1 else 0)
    (hk : ∀ k l, N.parameters.data.p k = N.parameters.data.p l →
      N.parameters.data.m k = N.parameters.data.m l)
    (hs : ∀ j, (∑ k, if N.parameters.data.p k = j then
      N.parameters.data.m k * (∑ l,
        (∑' n : ℕ, (N.parameters.data.P.transpose ^ n) k l) * N.parameters.data.lam l)
      else 0) < 1)
    (hp : ∀ κ : ℝ, 0 < κ →
      let A : Set S := {x | stateSize (N.coordinates x).val ≤ κ}
      A.Nonempty ∧ MeasurableSet A ∧
      ∃ a : Measure ℝ≥0, IsProbabilityMeasure a ∧ a {0} = 0 ∧
        ∃ ν : Measure S, ν ≠ 0 ∧ ∀ x ∈ A, ∀ B, MeasurableSet B →
          ν B ≤ ∫⁻ t, N.process.transition t x B ∂a) :
    (∃ φ : Measure S, φ ≠ 0 ∧ SigmaFinite φ ∧
      ∀ B, MeasurableSet B → 0 < φ B → ∀ x,
        ∀ᵐ ω ∂N.process.probability,
          (∫⁻ t : ℝ in Ici 0, B.indicator (fun _ => (1 : ℝ≥0∞))
            (N.process.path x (Real.toNNReal t) ω)) = ⊤) ∧
    (∃ π : Measure S, IsProbabilityMeasure π ∧
      ∀ t B, MeasurableSet B → π B = ∫⁻ x, N.process.transition t x B ∂π) := by sorry

end BramsonQueueing.FIFOKelly
