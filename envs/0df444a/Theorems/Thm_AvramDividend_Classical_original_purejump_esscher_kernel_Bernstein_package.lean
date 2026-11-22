-- Prove2me | Theorems.Thm_AvramDividend_Classical_original_purejump_esscher_kernel_Bernstein_package
-- name    : AvramDividend.Classical.original_purejump_esscher_kernel_Bernstein_package
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T15:48:49.227523+00:00
-- url     : https://prove2.me/theorems/cf031c6a-adb5-4cac-97a7-2fcaa865d74f
-- title:
--   Exact original UBV Lévy negative-tail Esscher kernel as an infinite-activity killed Bernstein measure
-- statement:
--   For the original standing spectrally negative pure-jump unbounded-variation Lévy process, fix positive φ with ψφ>0. Construct the EXACT Esscher-weighted original negative-tail kernel κ(dt)=1_{t>0} e^(−φt)ν((−∞,−t))dt and killing rate k=ψφ/φ. Prove κ is σ-finite, supported on positive t, absolutely continuous with respect to Lebesgue volume, and has infinite mass near zero. For every s>0 its compensated Bernstein integral is finite and 1/(k+∫(1−e^(−st))κ(dt))=(φ+s)/ψ(φ+s). This is the genuine process-to-analytic-kernel source, with no renewal potential or scale function assumed. It connects Proved 0cb20c38 and 8f9e6281 to the general killed-renewal potential source e58a6ed6.
-- source:
--   Proved original ψ/θ tail 0fded7ba, killed Bernstein shift 0cb20c38, lower positivity fd68d5d9, original Esscher kernel AC 501256a2, original UBV negative-tail infinite mass 8f9e6281, generic Esscher infinite origin mass 011d0df2, finite tail 8b87003a. Connects to general e58a6ed6 and fixed φ source original_purejump_positive_esscher_killed_potential_exists.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.original_purejump_esscher_kernel_Bernstein_package
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hσ : X.σ = 0)
    (φ : ℝ) (hφ : 0 < φ) (hψ : 0 < X.ψ φ) :
    ∃ (κ : Measure ℝ) (k : ℝ),
      κ = ((volume : Measure ℝ).withDensity
        (fun t : ℝ =>
          ENNReal.ofReal (Real.exp (-(φ * t))) *
            X.ν (Iio (-t)))).restrict (Ioi 0) ∧
      SFinite κ ∧ k = X.ψ φ / φ ∧ 0 < k ∧
      κ (Iic (0 : ℝ)) = 0 ∧
      κ ≪ (volume : Measure ℝ) ∧
      κ (Ioc (0 : ℝ) 1) = ⊤ ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ t : ℝ,
          ENNReal.ofReal (1 - Real.exp (-(s * t))) ∂κ) ≠ ⊤ ∧
        ENNReal.ofReal ((φ + s) / X.ψ (φ + s)) =
          (ENNReal.ofReal k +
            (∫⁻ t : ℝ,
              ENNReal.ofReal (1 - Real.exp (-(s * t))) ∂κ))⁻¹) := by sorry
