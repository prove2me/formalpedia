-- Prove2me | Theorems.Thm_DiscreteStability_trap
-- name    : DiscreteStability.trap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:43:06.697858+00:00
-- url     : https://prove2.me/theorems/5a99b374-4fe5-55c5-9257-ce91efea6475
-- title:
--   Discrete Stability: trap
-- statement:
--   The barrier construction in the proof of Theorem 5.1(i): for every `R > 0` there are
--   `0 < ρ ≤ R` and `δ > 0` such that every orbit started in `B_δ(x̄)` stays in `B_ρ(x̄)`,
--   and every step satisfies the weighted ascent inequality.
--
--   Source: https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Stability.lean#L71-L172
-- source:
--   https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Stability.lean#L71-L172

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

theorem DiscreteStability.trap (hH : LocalHyp f g xbar r₀ L) (hP : ∀ k, StepBound (P k) (lo k) (hi k))
    (hΛ : ∀ k, hi k ≤ Λ) (hS1 : L * Λ ≤ 2) (hH1 : IsolatedMax f xbar) {R : ℝ} (hR : 0 < R) :
    ∃ ρ, 0 < ρ ∧ ρ ≤ R ∧ ρ ≤ r₀ ∧ (∀ y, y ≠ xbar → dist y xbar ≤ ρ → f y < f xbar) ∧
      ∃ δ > 0, ∀ (k₀ : ℕ) (x : ℕ → E), IsOrbit P g k₀ x → dist (x k₀) xbar < δ →
        ∀ k ≥ k₀, dist (x k) xbar < ρ ∧
          f (x k) + lo k * (2 - L * hi k) / 2 * ‖g (x k)‖ ^ 2 ≤ f (x (k + 1)) := by sorry
