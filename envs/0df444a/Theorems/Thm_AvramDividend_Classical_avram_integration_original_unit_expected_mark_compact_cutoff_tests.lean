-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_integration_original_unit_expected_mark_compact_cutoff_tests
-- name    : AvramDividend.Classical.avram_integration_original_unit_expected_mark_compact_cutoff_tests
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:30:35.407196+00:00
-- url     : https://prove2.me/theorems/e414d4e7-a082-4208-924a-187a05a4ac73
-- title:
--   Original intrinsic negative-cutoff mean measure agrees with Levy measure on compact continuous tests
-- statement:
--   For the original spectrally negative Levy process, assume rho is precisely its unit-time expected intrinsic marked jump measure and has finite mass on the negative cutoff. Every real compactly supported continuous test has the same integral against rho and the original Levy measure after restricting to that cutoff. This is the analytic compact-test obligation needed by the independently Proved original compact-test-to-Borel theorem.
-- source:
--   Original source positive compact jump L1 and lintegral theorem a09f7014-b563-4d3a-9911-03825b524893, original mean mark measure 9bbf7f85-18e1-4606-9d47-36dd5920b91d and count-map test lintegral bd88fc0b-eb07-4064-8135-843eaca58ffa supply independent inputs. Remaining challenge is the actual Tonelli/approximation and signed compact test interchange. Intended consumer 6169a734-f844-4e24-b278-0713a6f113b9, with Proved Radon/Borel bridge 12ba55c4-ec12-4314-ae60-e5f7fd390999.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_integration_original_unit_expected_mark_compact_cutoff_tests
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε)
    (ρ : Measure ℝ)
    (hρ : ∀ B : Set ℝ, MeasurableSet B →
      ρ B = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P))
    (hρfinite : ρ (Iic (-ε)) ≠ ⊤) :
    ∀ g : CompactlySupportedContinuousMap ℝ ℝ,
      (∫ y : ℝ, g y ∂(ρ.restrict (Iic (-ε)))) =
        (∫ y : ℝ, g y ∂(X.ν.restrict (Iic (-ε)))) := by sorry
