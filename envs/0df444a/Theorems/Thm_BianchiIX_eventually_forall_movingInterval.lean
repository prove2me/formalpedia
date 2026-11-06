-- Prove2me | Theorems.Thm_BianchiIX_eventually_forall_movingInterval
-- name    : BianchiIX.eventually_forall_movingInterval
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T22:42:21.352405+00:00
-- url     : https://prove2.me/theorems/eed5e345-b01f-4c06-a2a6-ac0b74a72af6
-- title:
--   Uniform persistence on a continuously varying compact time interval
-- statement:
--   Let $X$ be a topological space, $x_0\in X$, and
--   $T:X\to\mathbb R$ be continuous at $x_0$, with $T(x_0)>0$.
--   Let $P(x,t)$ be a predicate such that, for each $t\in[0,T(x_0)]$,
--   $P(y,s)$ holds for all $(y,s)$ sufficiently near $(x_0,t)$.
--   Then for all $x$ sufficiently near $x_0$,
--   $$P(x,t)\quad\hbox{for every }t\in[0,T(x)].$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/FirstReturnPersistence.lean#L15-L33

import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology
variable {X : Type*} [TopologicalSpace X]

theorem BianchiIX.eventually_forall_movingInterval {x₀ : X} {T : X → ℝ} {P : X → ℝ → Prop}
    (hT : ContinuousAt T x₀) (hpos : 0 < T x₀)
    (hP : ∀ t ∈ Icc 0 (T x₀), ∀ᶠ z : X × ℝ in 𝓝 (x₀, t), P z.1 z.2) :
    ∀ᶠ x in 𝓝 x₀, ∀ t ∈ Icc 0 (T x), P x t := by sorry
