-- Prove2me | Theorems.Thm_DiscreteStability_tendsto_of_weighted_ascent
-- name    : DiscreteStability.tendsto_of_weighted_ascent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:43:15.277225+00:00
-- url     : https://prove2.me/theorems/a5155028-17cc-54bd-93a3-922cfc0b5da5
-- title:
--   Discrete Stability: tendsto of weighted ascent
-- statement:
--   The convergence half of the proofs of Theorem 5.1(ii), Corollary 5.2 and Theorem 6.1:
--   if the iterates stay in a compact set `T` on which `x̄` is the unique maximizer of `f` and the
--   unique zero of `g`, and each step gains at least `w k ‖g (x k)‖²` with `∑ w k = ∞`,
--   then `x k → x̄`.
--
--   Source: https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Stability.lean#L187-L280
-- source:
--   https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Stability.lean#L187-L280

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
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem DiscreteStability.tendsto_of_weighted_ascent {T : Set E} (hT : IsCompact T) (hxbarT : xbar ∈ T)
    (hf : ContinuousOn f T) (hg : ContinuousOn g T)
    (hflt : ∀ y ∈ T, y ≠ xbar → f y < f xbar) (hgne : ∀ y ∈ T, y ≠ xbar → g y ≠ 0)
    {w : ℕ → ℝ} (hw0 : ∀ k, 0 ≤ w k)
    (hw : Tendsto (fun N => ∑ k ∈ Finset.range N, w k) atTop atTop)
    {x : ℕ → E} {k₀ : ℕ} (hxT : ∀ k ≥ k₀, x k ∈ T)
    (hasc : ∀ k ≥ k₀, f (x k) + w k * ‖g (x k)‖ ^ 2 ≤ f (x (k + 1))) :
    Tendsto x atTop (𝓝 xbar) := by sorry
