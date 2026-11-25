-- Prove2me | Theorems.Thm_DiscreteStability_asympStable_weighted
-- name    : DiscreteStability.asympStable_weighted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:44:21.99693+00:00
-- url     : https://prove2.me/theorems/4d95bac7-03b6-4482-a38a-92af06586fce
-- title:
--   Discrete Stability: asymp Stable weighted
-- statement:
--   **Corollary 5.2.** Under H0_Δ, H1, H2, S1 and the weighted divergence condition
--   `∑ λ₁(P_k) (2 - L λₙ(P_k)) = ∞`, `x̄` is uniformly asymptotically stable.
--
--   Source: https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Stability.lean#L284-L312
-- source:
--   https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Stability.lean#L284-L312

import Definitions.Def_DiscreteStability_Ascent
import Definitions.Def_DiscreteStability_Stability
set_option autoImplicit true
open scoped RealInnerProductSpace Topology
open Set Metric Filter
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {xbar : E} {r₀ L Λ : ℝ}
  {P : ℕ → E →L[ℝ] E} {lo hi : ℕ → ℝ}
variable [FiniteDimensional ℝ E]

theorem DiscreteStability.asympStable_weighted (hH : LocalHyp f g xbar r₀ L)
    (hP : ∀ k, StepBound (P k) (lo k) (hi k)) (hΛ : ∀ k, hi k ≤ Λ) (hS1 : L * Λ ≤ 2)
    (hH1 : IsolatedMax f xbar) (hH2 : IsolatedCrit g xbar)
    (hW : Tendsto (fun N => ∑ k ∈ Finset.range N, lo k * (2 - L * hi k)) atTop atTop) :
    UniformlyAsympStable P g xbar := by sorry
