-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_original_compact_test_to_separated_borel_rate
-- name    : AvramDividend.Classical.avram_p2_d_future_original_compact_test_to_separated_borel_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:15:22.478307+00:00
-- url     : https://prove2.me/theorems/12ba55c4-ec12-4314-ae60-e5f7fd390999
-- title:
--   Original intrinsic Borel rate from compact tests of finite-band mean measure
-- statement:
--   For original spectrally negative Lévy X, given the genuine unit-time mean mark measure ρ, its regularity on a finite negative band, and equality of all compactly supported continuous test integrals with the original ν, derive exact expected intrinsic jump counts for every Borel subset of that separated band. The compact-test integral equality is an explicit still-open analytic premise.
-- source:
--   Original Proved negative-band ν finiteness 86086cb2-e1cd-4ed8-a49b-7f8eefc9842b and pinned Mathlib Measure.ext_of_integral_eq_on_compactlySupported. Regularity of ρ and compact-test equality are explicit premises.

import Mathlib.Topology.Order.LeftRightLim
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_original_compact_test_to_separated_borel_rate
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
    (hregρ : (ρ.restrict (Iic (-ε))).Regular)
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
