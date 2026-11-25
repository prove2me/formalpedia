-- Prove2me | Theorems.Thm_DiscreteStability_basin
-- name    : DiscreteStability.basin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:48:55.515138+00:00
-- url     : https://prove2.me/theorems/ec5dec97-66ca-42a4-9548-f0f9f95191fc
-- title:
--   Discrete Stability: basin
-- statement:
--   **Theorem 6.1.** Every orbit of (Δ) started in `U = E_c` stays in `U` and converges to `x̄`;
--   that is, `E_c` lies in the basin of attraction of `x̄`.
--
--   Source: https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Basin.lean#L30-L120
-- source:
--   https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Basin.lean#L30-L120

import Definitions.Def_DiscreteStability_Stability
import Definitions.Def_DiscreteStability_Basin
set_option autoImplicit true
open scoped RealInnerProductSpace Topology
open Set Metric Filter
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {f : E → ℝ} {g : E → E} {xbar : E} {L Λ c η : ℝ}
  {P : ℕ → E →L[ℝ] E} {lo hi : ℕ → ℝ}

theorem DiscreteStability.basin {U : Set E} (hU : IsOpen U) (hxU : xbar ∈ U) (hcomp : IsCompact (closure U))
    (hgrad : ∀ z ∈ closure U, HasFDerivAt f (innerSL ℝ (g z)) z)
    (hL : 0 ≤ L) (hlip : ∀ u ∈ closure U, ∀ v ∈ closure U, ‖g u - g v‖ ≤ L * ‖u - v‖)
    (hc : ∀ y ∈ U, c < f y) (hM : ∀ y ∈ U, y ≠ xbar → f y < f xbar)
    (hH5 : ∀ y ∈ frontier U, f y = c) (hH6 : ∀ y ∈ closure U, y ≠ xbar → g y ≠ 0)
    (hP : ∀ k, StepBound (P k) (lo k) (hi k)) (hΛ : ∀ k, hi k ≤ Λ)
    (hη : 0 < η) (hS3 : L * Λ ≤ 2 - η)
    (hH3 : Tendsto (fun N => ∑ k ∈ Finset.range N, lo k) atTop atTop) :
    ∀ (k₀ : ℕ) (x : ℕ → E), IsOrbit P g k₀ x → x k₀ ∈ U →
      (∀ k ≥ k₀, x k ∈ U) ∧ Tendsto x atTop (𝓝 xbar) := by sorry
