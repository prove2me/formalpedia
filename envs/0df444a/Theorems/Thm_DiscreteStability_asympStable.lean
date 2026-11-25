-- Prove2me | Theorems.Thm_DiscreteStability_asympStable
-- name    : DiscreteStability.asympStable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T08:48:02.943126+00:00
-- url     : https://prove2.me/theorems/5759f0e0-728e-457f-82b8-27268de85d9a
-- title:
--   Discrete Stability: asymp Stable
-- statement:
--   **Theorem 5.1(ii).** Under H0_Δ, H1, H2, H3_Δ and S2, `x̄` is uniformly asymptotically
--   stable. (H3_Δ is stated for the lower bounds `lo k ≤ λ₁(P_k)`; taking `lo k = λ₁(P_k)` gives
--   the paper's `∑ λ₁(P_k) = ∞`.)
--
--   Source: https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Stability.lean#L317-L330
-- source:
--   https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Stability.lean#L317-L330

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

theorem DiscreteStability.asympStable (hH : LocalHyp f g xbar r₀ L) (hP : ∀ k, StepBound (P k) (lo k) (hi k))
    (hΛ : ∀ k, hi k ≤ Λ) {η : ℝ} (hη : 0 < η) (hS2 : L * Λ ≤ 2 - η)
    (hH1 : IsolatedMax f xbar) (hH2 : IsolatedCrit g xbar)
    (hH3 : Tendsto (fun N => ∑ k ∈ Finset.range N, lo k) atTop atTop) :
    UniformlyAsympStable P g xbar := by sorry
