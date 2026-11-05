-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_public_original_rate_from_compact_band_tests
-- name    : AvramDividend.Classical.avram_p2_j_ui_public_original_rate_from_compact_band_tests
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:26:47.702746+00:00
-- url     : https://prove2.me/theorems/7f13f7cf-5c51-4338-81dc-cdc41f5e1b2d
-- title:
--   Public finite-intensity compact-test identification of genuine original separated Borel jump rates
-- statement:
--   For the original intrinsic jump-count intensity represented by a measure rho, assume its genuine unit-horizon count identity, finite mass on one separated negative band, and equality of rho and original Levy measure X.nu integrals against every compactly supported continuous real test on that band. Prove their equality on all measurable Borel subsets of the band. The finite-mass hypothesis yields regularity automatically; this supplies a public measure-uniqueness bridge without assuming Borel equality as a premise. The substantive remaining upstream obligation is compact-test equality for the original count intensity.

import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_j_ui_public_original_rate_from_compact_band_tests
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε)
    (ρ : Measure ℝ)
    (hρ : ∀ B : Set ℝ, MeasurableSet B →
      ρ B = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P))
    (hρfin : ρ (Iic (-ε)) < ⊤)
    (hTests : ∀ g : CompactlySupportedContinuousMap ℝ ℝ,
      (∫ y : ℝ, g y ∂(ρ.restrict (Iic (-ε)))) =
      (∫ y : ℝ, g y ∂(X.ν.restrict (Iic (-ε))))) :
    ∀ B : Set ℝ, MeasurableSet B → B ⊆ Iic (-ε) →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) = X.ν B := by sorry
