-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_scaled_deterministic_data
-- name    : AvramDividend.Classical.bv_ac_esscher_scaled_deterministic_data
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:07:50.286588+00:00
-- url     : https://prove2.me/theorems/b253bdd4-8df3-4ee1-b2c9-294d7f8df760
-- title:
--   Complete analytic kernel and convolution-power data for the corrected BV Esscher renewal scale theorem
-- statement:
--   Construct all non-stochastic witnesses and prove every deterministic conjunct of the corrected BV Esscher scale-function renewal-data theorem (9be5ada9-6f14-4f14-8115-14262e488433), including a positive Esscher root, a strictly subunit positive kernel, global kernel integrability, continuity, causality and local boundedness, a full recursive convolution-power family, geometric pointwise bounds, positivity and arbitrary-scalar shifted-density integrability from zero. The only remaining ingredient of the parent is the exact tilted-scale renewal-integral identity. This directly composes canonically Proved kernel_analytic_data and causal_subunit_renewal_full_real_power_package.
-- source:
--   Proved BV Esscher analytic kernel package and the Proved full real convolution-power package.

import Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_kernel_analytic_data
import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_full_real_power_package
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_ac_esscher_scaled_deterministic_data
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hbv : X.BoundedVariation) :
    ∃ (φ ρ : ℝ) (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ),
      0 < φ ∧ X.ψ φ = q ∧ 0 < ρ ∧ ρ < 1 ∧
      Integrable κ volume ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, x ≤ 0 → κ x = 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |κ x| ≤ M) ∧
      F 0 = κ ∧
      (∀ n : ℕ, F (n + 1) =
        fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 < x →
        F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) ∧
      (∀ b : ℝ, ∀ x : ℝ, 0 < x →
        IntervalIntegrable
          (fun y : ℝ => b * ∑' n : ℕ,
            if n = 0 then (0 : ℝ) else F (n - 1) y) volume 0 x) := by sorry
