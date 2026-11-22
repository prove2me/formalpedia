-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_path_killed_scale_scalar_no_standing_public
-- name    : AvramDividend.Classical.p2m81_bv_path_killed_scale_scalar_no_standing_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T22:33:10.619325+00:00
-- url     : https://prove2.me/theorems/2db70736-a2ce-4019-9dfa-f44b6c0aea42
-- title:
--   Standing-free bounded-variation killed scale identity on path space
-- statement:
--   For a spectrally negative Levy process of bounded variation with a positive q-root phi, the history-killed discounted q-scale reward at deterministic horizon T has expectation W(x) in the law of the whole path. This replaces the Standing-based deterministic semigroup and real-to-lintegral bridge by the proved positive-root semigroup and the generic growth-witness bridge.
-- source:
--   Adapted from exact accepted source cfed60ac... of b1285a5a by replacing the Standing deterministic killed semigroup with 094049ef and the Standing real-to-ENNReal bridge with the generic growth-witness bridge af571454, using theta=phi+1 and levy_psi_root_shifted_increment_lower.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_deterministic_killed_qscale
import Theorems.Thm_AvramDividend_Classical_chat04_history_killed_scale_real_ennreal_integral_bridge
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_shifted_increment_lower
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_closed_survival_schedule_iff
import Theorems.Thm_AvramDividend_Classical_chat04_countable_shifted_future_reserve_survival_measurable
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.p2m81_bv_path_killed_scale_scalar_no_standing_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (x : ℝ) (T : ℝ≥0) (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = T) :
    (∫⁻ y : ℝ≥0 → ℝ,
      if ∀ j : ℕ, τ j ≤ T → 0 ≤ x + y (τ j) then
        ENNReal.ofReal (Real.exp (-(q * (T : ℝ))) * W (x + y T))
      else (0 : ℝ≥0∞)
      ∂(Measure.map (fun ω : Ω => (fun t : ℝ≥0 => X.X t ω)) P)) =
    ENNReal.ofReal (W x) := by sorry
