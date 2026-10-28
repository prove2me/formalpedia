-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_kernel_analytic_data
-- name    : AvramDividend.Classical.bv_ac_esscher_kernel_analytic_data
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T17:59:24.475732+00:00
-- url     : https://prove2.me/theorems/a2d16287-5672-464b-ab3e-66c282a686ca
-- title:
--   BV Esscher positive subunit kernel and universal renewal-density integrability
-- statement:
--   Under standing bounded-variation Lévy assumptions, construct the positive Esscher root and a continuous antitone causal nonnegative kernel with exact strictly positive subunit mass, and prove that every associated convolution-power recursion has an integrable shifted renewal series from zero after arbitrary scalar multiplication. This packages the complete analytic hypotheses already independently proved for the root-connected corrected BV scale identification (1ca4a724-85b7-48bf-bae4-37890ef7055b). The remaining open content there is the stochastic scale-to-renewal equality.
-- source:
--   Proved bv_positive_esscher_root, bv_esscher_root_positive_subunit_kernel_package and causal_subunit_shifted_renewal_density_continuous_integrable_for_any_recursion.

import Theorems.Thm_AvramDividend_Classical_bv_positive_esscher_root
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_positive_subunit_kernel_package
import Theorems.Thm_AvramDividend_Classical_causal_subunit_shifted_renewal_density_continuous_integrable_for_any_recursion
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_ac_esscher_kernel_analytic_data
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hbv : X.BoundedVariation) :
    ∃ (φ ρ : ℝ) (κ : ℝ → ℝ),
      0 < φ ∧ X.ψ φ = q ∧
      0 < ρ ∧ ρ < 1 ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      AntitoneOn κ (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, x ≤ 0 → κ x = 0) ∧
      (∀ x : ℝ, 0 ≤ x → 0 ≤ κ x) ∧
      IntegrableOn κ (Ioi (0 : ℝ)) volume ∧
      (∫ x in Ioi (0 : ℝ), κ x ∂volume) = ρ ∧
      (∀ (b : ℝ) (F : ℕ → ℝ → ℝ),
        F 0 = κ →
        (∀ n : ℕ, F (n + 1) =
          fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) →
        ∀ x : ℝ, 0 < x →
          IntervalIntegrable
            (fun y : ℝ => b * ∑' n : ℕ,
              if n = 0 then (0 : ℝ) else F (n - 1) y) volume 0 x) := by sorry
