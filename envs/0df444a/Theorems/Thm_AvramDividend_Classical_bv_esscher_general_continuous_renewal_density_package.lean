-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_general_continuous_renewal_density_package
-- name    : AvramDividend.Classical.bv_esscher_general_continuous_renewal_density_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:09:11.89511+00:00
-- url     : https://prove2.me/theorems/f7ab74c3-b450-48ad-927b-adff6ee29d27
-- title:
--   General bounded-variation Esscher renewal density is continuous and integrable to zero
-- statement:
--   For any standing bounded-variation spectrally negative Lévy process with positive discount, construct a positive Esscher root, exact drift-normalised canonical jump-tail kernel, subcritical mass and a continuously summed geometric renewal density integrable on intervals starting at zero. The theorem requires no absolute-continuity hypothesis on the Lévy jump measure. It supplies the whole analytic half of the canonical scale-function renewal representation.
-- source:
--   Proved positive Esscher root (3f64cde9), positive subunit kernel package (7d3344ce), causal_subunit_shifted_renewal_density_continuous_integrable_at_zero (84fff55b).

import Theorems.Thm_AvramDividend_Classical_bv_positive_esscher_root
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_positive_subunit_kernel_package
import Theorems.Thm_AvramDividend_Classical_causal_subunit_shifted_renewal_density_continuous_integrable_at_zero
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- The canonical Esscher kernel has a continuous, origin-integrable renewal density without jump-density assumptions. -/
theorem bv_esscher_general_continuous_renewal_density_package
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hbv : X.BoundedVariation) :
    ∃ (φ : ℝ) (κ : ℝ → ℝ) (ρ : ℝ) (F : ℕ → ℝ → ℝ),
      0 < φ ∧ X.ψ φ = q ∧
      (∀ t : ℝ, κ t = if 0 < t then
        ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
          (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
          {z : ℝ≥0 | t < (z : ℝ)}) / X.drift else 0) ∧
      0 < ρ ∧ ρ < 1 ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      AntitoneOn κ (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, x ≤ 0 → κ x = 0) ∧
      (∀ x : ℝ, 0 ≤ κ x) ∧
      IntegrableOn κ (Ioi (0 : ℝ)) volume ∧
      (∫ x in Ioi (0 : ℝ), κ x ∂volume) = ρ ∧
      F 0 = κ ∧
      (∀ n : ℕ, F (n + 1) =
        fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) ∧
      ContinuousOn
        (fun x : ℝ => ∑' n : ℕ,
          if n = 0 then (0 : ℝ) else F (n - 1) x)
        (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, 0 < x →
        IntervalIntegrable
          (fun y : ℝ => ∑' n : ℕ,
            if n = 0 then (0 : ℝ) else F (n - 1) y)
          volume 0 x) := by sorry

end AvramDividend.Classical
