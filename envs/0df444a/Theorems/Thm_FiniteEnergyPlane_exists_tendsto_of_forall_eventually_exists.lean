-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_tendsto_of_forall_eventually_exists
-- name    : FiniteEnergyPlane.exists_tendsto_of_forall_eventually_exists
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-05T20:17:50.618017+00:00
-- url     : https://prove2.me/theorems/c59ebf36-185b-43f0-ae5f-a55162503120
-- title:
--   Extracting convergent sequences from solutions in shrinking balls
-- statement:
--   Let $X,Y$ be pseudometric spaces, $x_0\in X$, $y_0\in Y$, and $P_k\subseteq X\times Y$ relations, $k\in\mathbb{N}$. Suppose that for every $\delta>0$, for all large $k$ there is $(x,y)\in P_k$ with $d(x,x_0)<\delta$ and $d(y,y_0)<\delta$. Then there are sequences $x_k\to x_0$ and $y_k\to y_0$ with $(x_k,y_k)\in P_k$ for all large $k$.
--
--   Role: turns an $\varepsilon$-$\delta$ form of an existence statement into a statement about convergent sequences.
-- source:
--   Standard diagonal argument in metric spaces

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic

namespace FiniteEnergyPlane

open Metric Filter Topology

/-- If for every `δ > 0` the relation `P k` eventually has a solution in `B(x₀, δ) × B(y₀, δ)`, then
there are sequences `x k → x₀`, `y k → y₀` with `P k (x k) (y k)` for all large `k`. -/
theorem exists_tendsto_of_forall_eventually_exists {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] (P : ℕ → X → Y → Prop) (x₀ : X) (y₀ : Y)
    (h : ∀ δ > (0 : ℝ), ∀ᶠ k in atTop, ∃ x ∈ ball x₀ δ, ∃ y ∈ ball y₀ δ, P k x y) :
    ∃ (x : ℕ → X) (y : ℕ → Y), Tendsto x atTop (𝓝 x₀) ∧ Tendsto y atTop (𝓝 y₀) ∧
      ∀ᶠ k in atTop, P k (x k) (y k) := by
  sorry

end FiniteEnergyPlane
